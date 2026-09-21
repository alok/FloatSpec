#!/usr/bin/env python3
"""Fail-closed checks for the dependency/declaration queue's evidence boundaries."""

import hashlib
import unittest

from flocq_port_queue import annotate, parse_glob, validate_order, validate_compiled_anchors


class QueueTests(unittest.TestCase):
    def glob(self, source, lines):
        return "DIGEST " + hashlib.md5(source).hexdigest() + "\nFFlocq.Core.Example\n" + lines

    def test_source_order_uses_byte_offsets_and_preserves_kinds(self):
        source = "(* π *)\nDefinition foo := 0.\nLemma bar : True.\n".encode()
        foo, bar = source.index(b"foo"), source.index(b"bar")
        glob = self.glob(source, f"prf {bar}:{bar+2} <> bar\ndef {foo}:{foo+2} <> foo\n"
                         "R0:1 Stdlib.Reals.Reals <> <> lib\nbinder 0:1 <> ignored\n")
        rows, imports = parse_glob(source, glob, "src/Core/Example.v")
        self.assertEqual([(r['name'], r['line'], r['kind']) for r in rows],
                         [('foo', 2, 'def'), ('bar', 3, 'prf')])
        self.assertEqual(imports, ['Stdlib.Reals.Reals'])

    def test_stale_digest_unknown_kind_bad_span_and_duplicate_rejected(self):
        source = b"Definition foo := 0."
        for data in ("DIGEST stale\n", self.glob(source, "newkind 11:13 <> foo"),
                     self.glob(source, "def 11:99 <> foo"),
                     self.glob(source, "def 11:13 <> foo\ndef 11:13 <> foo")):
            with self.subTest(data=data), self.assertRaises(ValueError):
                parse_glob(source, data, "src/Foo.v")

    def test_unsupported_mutual_group_is_not_silently_linearized(self):
        source = b"Fixpoint foo := 0\nwith bar := 1."
        with self.assertRaisesRegex(ValueError, "mutual"):
            parse_glob(source, self.glob(source, "def 9:11 <> foo"), "src/Foo.v")

    def test_record_facets_at_one_token_are_one_source_declaration(self):
        source = b"Class foo := bar : True."
        rows, _ = parse_glob(source, self.glob(source,
            "ind 6:8 <> foo\nrec 6:8 <> foo\nconstr 13:15 <> bar\nproj 13:15 <> bar"),
            "src/Foo.v")
        self.assertEqual([d['kind'] for d in rows], ['ind+rec', 'constr+proj'])

    def test_local_alias_reuse_has_distinct_source_ids(self):
        source = b"Notation foo := 0.\nNotation foo := 1."
        rows, _ = parse_glob(source, self.glob(source,
            "abbrev 9:11 <> foo\nabbrev 28:30 <> foo"), "src/Foo.v")
        self.assertEqual(len(rows), 2)
        self.assertNotEqual(rows[0]['id'], rows[1]['id'])
        self.assertEqual(rows[0]['source_key'], rows[1]['source_key'])

    def test_topological_order_rejects_cycles_missing_edges_and_duplicates(self):
        validate_order(['a', 'b', 'c'], {'a': [], 'b': ['a'], 'c': ['a']})
        for order, graph in ((['b', 'a'], {'a': [], 'b': ['a']}),
                             (['a'], {'a': ['a']}), (['a'], {'a': ['missing']}),
                             (['a', 'a'], {'a': []}), (['a'], {'a': [], 'b': []})):
            with self.subTest(order=order, graph=graph), self.assertRaises(ValueError):
                validate_order(order, graph)

    def test_anchor_requires_compiled_declaration_not_comment_text(self):
        modules = [{'path': 'src/Foo.v', 'declarations': [{'line': 3, 'name': 'foo'}]}]
        valid = {'path': 'src/Foo.v', 'line': 3, 'name': 'foo'}
        validate_compiled_anchors(modules, [valid])
        for change in ({'line': 2}, {'name': 'bar'}, {'path': 'src/Bar.v'}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_compiled_anchors(modules, [valid | change])

    def inputs(self):
        modules = [{'declarations': [{'id': 'src/Foo.v:foo', 'name': 'foo'}]}]
        inventory = {'declarations': [{'name': name, 'type_hash': '1', 'value_hash': '2',
                                      'noncomputable': False} for name in ['A.foo', 'B.foo']],
                     'references': [{'path': 'src/Foo.v', 'name': 'foo', 'lean_name': 'A.foo'}]}
        return modules, inventory

    def test_compiled_candidates_and_anchors_are_never_automatic_review(self):
        modules, inventory = self.inputs()
        annotate(modules, inventory, [])
        row = modules[0]['declarations'][0]
        self.assertEqual(row['anchors'], ['A.foo'])
        self.assertEqual(row['name_candidates'], ['A.foo', 'B.foo'])
        self.assertEqual(row['status'], 'unreviewed')
        self.assertIsNone(row['review'])

    def test_manual_review_requires_existing_compiled_names_and_evidence(self):
        modules, inventory = self.inputs()
        review = {'source_id': 'src/Foo.v:foo', 'status': 'reviewed-contract',
                  'scope': 'Test-only entry', 'lean_names': ['A.foo'],
                  'evidence': ['scripts/test_flocq_port_queue.py'],
                  'lean_fingerprints': {'A.foo': {'type_hash': '1', 'value_hash': '2',
                                                'noncomputable': False}}}
        annotate(modules, inventory, [review])
        self.assertEqual(modules[0]['declarations'][0]['status'], 'reviewed-contract')
        for replacement in ({'lean_names': ['Absent.foo']}, {'evidence': []},
                            {'evidence': ['absent']}, {'scope': ''},
                            {'status': 'proved-equivalent'}, {'source_id': 'src/Foo.v:absent'},
                            {'lean_fingerprints': {}}, {'lean_fingerprints': None}):
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                annotate(*self.inputs(), [review | replacement])
        with self.assertRaises(ValueError):
            annotate(*self.inputs(), [review, review])


if __name__ == '__main__':
    unittest.main()
