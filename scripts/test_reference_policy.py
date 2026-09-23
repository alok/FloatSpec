"""Mutation controls for admitting a pinned Flocq reference checkout.

Each control builds a throwaway Git repository shaped like a configured and
built Flocq checkout, so the policy is tested without a Rocq installation.
"""

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import zlib

import flocq_bridge as bridge


SOURCES = {
    ".gitignore": "*.vo\n*.vos\n*.vok\n*.glob\n.*.aux\n.*.cache\n/configure\n/config.status\n"
                  "/Remakefile\n/src/Version.v\n/examples/ComputeMore.v\n/html/\n",
    "configure.in": "AC_INIT([Flocq], [4.2.2],\n        [https://example.invalid/])\n"
                    "AC_CONFIG_FILES([Remakefile src/Version.v])\n",
    "Remakefile.in": "FILES = Core/Zaux.v Version.v\n",
    "src/Core/Zaux.v": "Definition Zaux := 0%Z.\n",
    "src/Version.v.in": 'Definition Flocq_version := "@PACKAGE_VERSION@".\n',
    "examples/Compute.v": "From Flocq Require Import Core.Zaux.\n",
}
VERSION = 'Definition Flocq_version := "4.2.2".\n'


def glob(source: str) -> str:
    """A .glob as coqc writes it: the first line is the MD5 of the compiled source."""
    return f"DIGEST {hashlib.md5(source.encode(), usedforsecurity=False).hexdigest()}\nF\n"


# What autoreconf, configure, remake, and remake check leave behind; none of it is tracked.
BUILD_PRODUCTS = {
    "configure": "#!/bin/sh\n",
    "config.status": 'S["COQC"]="/usr/bin/coqc"\n',
    "Remakefile": "FILES = Core/Zaux.v Version.v\n",
    "Makefile.coq": "all:\n",
    ".lia.cache": "",
    "src/Core/Zaux.vo": "",
    "src/Core/Zaux.vos": "",
    "src/Core/Zaux.vok": "",
    "src/Core/Zaux.glob": glob(SOURCES["src/Core/Zaux.v"]),
    "src/Core/.Zaux.aux": "",
    "src/Version.v": VERSION,
    "src/Version.vo": "",
    "src/Version.glob": glob(VERSION),
    "examples/Compute.vo": "",
    "examples/Compute.glob": glob(SOURCES["examples/Compute.v"]),
    "examples/ComputeMore.v": SOURCES["examples/Compute.v"],
}
GIT_ENV = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
           "GIT_AUTHOR_NAME": "policy", "GIT_AUTHOR_EMAIL": "policy@example.invalid",
           "GIT_COMMITTER_NAME": "policy", "GIT_COMMITTER_EMAIL": "policy@example.invalid"}
EDITED = "Definition Zaux := 1%Z.\n"


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True, env=GIT_ENV, timeout=30).stdout


def write(root: Path, files: dict[str, str]) -> None:
    for path, text in files.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)


class ReferencePolicyTests(unittest.TestCase):
    def directory(self) -> Path:
        directory = tempfile.TemporaryDirectory(prefix="floatspec-reference-policy-")
        self.addCleanup(directory.cleanup)
        return Path(directory.name).resolve()

    def reference(self) -> tuple[Path, str]:
        root = self.directory()
        git(root, "init", "-q")
        write(root, SOURCES)
        git(root, "add", "-A")
        git(root, "commit", "-q", "--no-verify", "-m", "pinned")
        write(root, BUILD_PRODUCTS)
        return root, git(root, "rev-parse", "HEAD").strip()

    def edited_commit(self, root: Path) -> str:
        """Commit an edited Zaux.v, leaving HEAD on it."""
        (root / "src/Core/Zaux.v").write_text(EDITED)
        git(root, "commit", "-q", "--no-verify", "-am", "edited")
        return git(root, "rev-parse", "HEAD").strip()

    def assert_hidden(self, root: Path) -> None:
        """Git itself reports a clean checkout."""
        self.assertEqual(git(root, "diff", "--name-only", "HEAD"), "")
        self.assertEqual(git(root, "diff", "--cached", "--name-only", "HEAD"), "")

    def assert_rejected(self, root: Path, pin: str, reason: str) -> None:
        with self.assertRaisesRegex(ValueError, reason):
            bridge.verify_reference(root, expected_pin=pin)

    def test_clean_reference_is_accepted_built_or_not(self):
        root, pin = self.reference()
        self.assertEqual(bridge.verify_reference(root, expected_pin=pin), pin)
        # The conformance loop verifies before it builds.
        for path in BUILD_PRODUCTS:
            (root / path).unlink()
        self.assertEqual(bridge.verify_reference(root, expected_pin=pin), pin)

    def test_wrong_pin_is_rejected(self):
        root, pin = self.reference()
        self.assert_rejected(root, "0" * len(pin), "does not match")
        git(root, "commit", "-q", "--no-verify", "--allow-empty", "-m", "later")
        self.assert_rejected(root, pin, "does not match")

    def test_default_pin_is_the_parent_gitlink(self):
        root, _ = self.reference()
        with self.assertRaisesRegex(ValueError, "gitlink"):
            bridge.verify_reference(root)

    def test_reference_must_be_its_own_work_tree(self):
        root, pin = self.reference()
        self.assert_rejected(root / "src", pin, "top level")
        # core.worktree would point Git's listings at a pristine copy while
        # coqc reads the directory that was passed in.
        pristine = self.directory()
        shutil.copytree(root, pristine, dirs_exist_ok=True, ignore=shutil.ignore_patterns(".git"))
        git(root, "config", "core.worktree", str(pristine))
        write(root, {"src/Core/Extra.v": "Axiom False_intro : False.\n"})
        self.assertNotIn("Extra.v", git(root, "ls-files", "--others"))
        self.assert_rejected(root, pin, "top level")

    def test_tracked_modifications_are_rejected(self):
        edits = {
            "source": lambda root: (root / "src/Core/Zaux.v").write_text(EDITED),
            "build input": lambda root: (root / "Remakefile.in").write_text("FILES = Core/Zaux.v\n"),
            "configure input": lambda root: (root / "configure.in").write_text("AC_INIT([Flocq], [9.9.9])\n"),
            "deletion": lambda root: (root / "src/Core/Zaux.v").unlink(),
            "mode": lambda root: (root / "src/Core/Zaux.v").chmod(0o755),
        }
        for label, edit in edits.items():
            with self.subTest(label=label):
                root, pin = self.reference()
                edit(root)
                self.assert_rejected(root, pin, "uncommitted tracked changes")

    def test_staged_changes_are_rejected(self):
        root, pin = self.reference()
        (root / "src/Core/Zaux.v").write_text(EDITED)
        git(root, "add", "src/Core/Zaux.v")
        self.assert_rejected(root, pin, "uncommitted tracked changes")
        # A staged edit whose working copy was restored is still not the pin.
        (root / "src/Core/Zaux.v").write_text(SOURCES["src/Core/Zaux.v"])
        self.assertEqual(git(root, "diff", "--name-only", "HEAD"), "")
        self.assert_rejected(root, pin, "uncommitted tracked changes")
        root, pin = self.reference()
        write(root, {"src/Core/Staged.v": "Definition staged := 0.\n"})
        git(root, "add", "src/Core/Staged.v")
        self.assert_rejected(root, pin, "uncommitted tracked changes")

    def test_edits_hidden_from_git_diff_are_rejected(self):
        def flag(option):
            def hide(root):
                git(root, "update-index", option, "src/Core/Zaux.v")
                (root / "src/Core/Zaux.v").write_text(EDITED)
            return hide

        def stale_stat(root):
            path, old = root / "src/Core/Zaux.v", (1_000_000_000, 1_000_000_000)
            git(root, "config", "core.trustctime", "false")
            git(root, "config", "core.checkStat", "minimal")
            os.utime(path, old)
            git(root, "update-index", "--refresh")
            path.write_text(EDITED)
            os.utime(path, old)

        def clean_filter(root):
            # Git hashes (and diffs) what the filter returns, not the bytes on disk.
            (root / ".git/info/attributes").write_text("*.v filter=pin\n")
            git(root, "config", "filter.pin.clean", "git cat-file blob HEAD:%f")
            (root / "src/Core/Zaux.v").write_text(EDITED)

        def ignored_mode(root):
            git(root, "config", "core.fileMode", "false")
            (root / "src/Core/Zaux.v").chmod(0o755)

        for label, hide in {"assume-unchanged": flag("--assume-unchanged"),
                            "skip-worktree": flag("--skip-worktree"),
                            "same size and mtime": stale_stat,
                            "clean filter": clean_filter,
                            "ignored file mode": ignored_mode}.items():
            with self.subTest(label=label):
                root, pin = self.reference()
                hide(root)
                self.assert_hidden(root)
                self.assert_rejected(root, pin, "differ from the pinned commit")

    def test_substituted_objects_are_rejected(self):
        # A replace ref keeps HEAD at the pin while Git reads another commit.
        root, pin = self.reference()
        edited = self.edited_commit(root)
        git(root, "checkout", "-q", "--detach", pin)
        git(root, "replace", pin, edited)
        git(root, "reset", "-q", "--hard", "HEAD")
        self.assertEqual(git(root, "rev-parse", "HEAD").strip(), pin)
        self.assertEqual((root / "src/Core/Zaux.v").read_text(), EDITED)
        self.assert_hidden(root)
        self.assert_rejected(root, pin, "uncommitted tracked changes")
        # Git verifies a commit's root tree when reading it, but not subtrees.
        root, pin = self.reference()
        edited = self.edited_commit(root)
        pinned, forged = (git(root, "rev-parse", f"{rev}:src/Core").strip() for rev in (pin, edited))
        content = subprocess.run(["git", "-C", str(root), "cat-file", "tree", forged], check=True,
                                 capture_output=True, env=GIT_ENV, timeout=30).stdout
        loose = root / ".git/objects" / pinned[:2] / pinned[2:]
        loose.chmod(0o644)
        loose.write_bytes(zlib.compress(b"tree %d\0" % len(content) + content))
        git(root, "checkout", "-q", "--detach", pin)
        (root / ".git/index").unlink()
        git(root, "reset", "-q", "--hard", pin)
        self.assertEqual(git(root, "rev-parse", "HEAD").strip(), pin)
        self.assertEqual((root / "src/Core/Zaux.v").read_text(), EDITED)
        self.assert_hidden(root)
        self.assert_rejected(root, pin, "object store does not match the pin")

    def test_untracked_and_ignored_rocq_sources_are_rejected(self):
        for label, path in {"untracked in src": "src/Core/Extra.v",
                            "untracked outside src": "examples/Extra.v",
                            "untracked at top level": "Extra.v",
                            "gitignored": "html/Extra.v",
                            "locally excluded": "src/Core/Local.v",
                            "fifo": "src/Core/Pipe.v"}.items():
            with self.subTest(label=label):
                root, pin = self.reference()
                (root / ".git/info/exclude").write_text("/src/Core/Local.v\n")
                if label == "fifo":
                    os.mkfifo(root / path)  # Git does not list it; reading it would block.
                else:
                    write(root, {path: "Axiom False_intro : False.\n"})
                self.assertEqual(label.startswith("untracked"),
                                 path in git(root, "ls-files", "--others", "--exclude-standard"))
                self.assert_rejected(root, pin, "untracked or ignored Rocq source")

    def test_generated_sources_must_match_their_templates(self):
        for path in ("src/Version.v", "examples/ComputeMore.v"):
            with self.subTest(path=path):
                root, pin = self.reference()
                (root / path).write_text("Axiom False_intro : False.\n")
                self.assert_rejected(root, pin, "untracked or ignored Rocq source")

    def test_nested_repository_is_rejected(self):
        root, pin = self.reference()
        git(root / "src", "init", "-q", "Nested")
        write(root, {"src/Nested/Hidden.v": "Axiom False_intro : False.\n"})
        self.assert_rejected(root, pin, "nested repository")

    def test_symlinks_are_rejected(self):
        outside = self.directory()
        write(outside, {"Hidden.v": "Axiom False_intro : False.\n"})

        def move_away(path):
            def hide(root):
                git(root, "update-index", "--skip-worktree", "src/Core/Zaux.v")
                target = outside / path.replace("/", "_")
                shutil.move(root / path, target)
                (root / path).symlink_to(target)
            return hide

        cases = {
            "untracked directory": (lambda root: (root / "src/Linked").symlink_to(outside), "symlink"),
            "dangling editor lock": (lambda root: (root / "src/Core/.#Zaux.v").symlink_to("user@host.1:0"),
                                     "symlink"),
            "pinned file": (move_away("src/Core/Zaux.v"), "not a regular file"),
            "pinned directory": (move_away("src/Core"), "not a regular file"),
        }
        for label, (link, reason) in cases.items():
            with self.subTest(label=label):
                root, pin = self.reference()
                link(root)
                self.assert_rejected(root, pin, reason)

    def test_stale_build_products_are_rejected(self):
        def rebuilt_then_reverted(root):
            write(root, {"src/Core/Zaux.glob": glob(EDITED)})

        cases = {
            "edit built then reverted": rebuilt_then_reverted,
            "generated source": lambda root: write(root, {"src/Version.glob": glob("old version")}),
            "example": lambda root: write(root, {"examples/Compute.glob": glob("old example")}),
            "missing glob": lambda root: (root / "src/Core/Zaux.glob").unlink(),
            "orphan object": lambda root: write(root, {"src/Core/Removed.vo": ""}),
        }
        for label, stale in cases.items():
            with self.subTest(label=label):
                root, pin = self.reference()
                stale(root)
                self.assert_rejected(root, pin, "compiled from other sources")


class ConfiguredCompilerTests(unittest.TestCase):
    def test_missing_compiler_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix="floatspec-reference-coqc-") as directory:
            root = Path(directory)
            with self.assertRaises(FileNotFoundError):
                bridge.configured_coqc(root)
            (root / "config.status").write_text(f'S["COQC"]="{root / "missing" / "coqc"}"\n')
            with self.assertRaisesRegex(ValueError, "configured COQC is unavailable"):
                bridge.configured_coqc(root)
            (root / "config.status").write_text('S["CAMLC"]="ocamlc"\n')
            with self.assertRaisesRegex(ValueError, "configured COQC is unavailable"):
                bridge.configured_coqc(root)
            (root / "coqc").write_text("")
            (root / "config.status").write_text(f'S["COQC"]="{root / "coqc"}"\n')
            self.assertEqual(bridge.configured_coqc(root), str(root / "coqc"))


if __name__ == "__main__":
    unittest.main()
