#!/usr/bin/env python3
"""Negative controls for the scoped release's source and kernel-evidence guards."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import verify_release as release


class ReleaseSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = json.loads((release.ROOT / release.MANIFEST).read_text())
        names = (set(self.manifest['mathematical_sources']) |
                 set(self.manifest['support_files']) | {release.MANIFEST})
        for name in names:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(release.ROOT / name, target)

    def test_current_source_package_is_accepted(self):
        self.assertEqual(release.check_sources(self.root), self.manifest)

    def test_same_named_true_theorem_is_rejected_even_if_manifest_hash_is_renewed(self):
        name = next(n for n in self.manifest['mathematical_sources'] if n.startswith('QIT/Coding/Private/'))
        replacement = b'theorem receiver_heralded : True := by trivial\n'
        (self.root / name).write_bytes(replacement)
        self.manifest['mathematical_sources'][name] = hashlib.sha256(replacement).hexdigest()
        (self.root / release.MANIFEST).write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(RuntimeError, 'preserved source review'):
            release.check_sources(self.root)

    def test_uncited_foundational_helper_cannot_change(self):
        name = next(n for n in self.manifest['mathematical_sources']
                    if not n.startswith('QIT/Coding/Private/'))
        with (self.root / name).open('a') as f:
            f.write('\naxiom unproved : False\n')
        with self.assertRaisesRegex(RuntimeError, 'source mismatch'):
            release.check_sources(self.root)

    def test_untracked_import_candidate_is_rejected(self):
        (self.root / 'QIT/Injected.lean').write_text('axiom unproved : False\n')
        with self.assertRaisesRegex(RuntimeError, 'source mismatch'):
            release.check_sources(self.root)

    def test_missing_source_is_rejected(self):
        name = next(iter(self.manifest['mathematical_sources']))
        (self.root / name).unlink()
        with self.assertRaisesRegex(RuntimeError, 'source mismatch'):
            release.check_sources(self.root)

    def test_weakening_literal_audit_is_rejected(self):
        (self.root / 'Check.lean').write_text('example : True := by trivial\n')
        with self.assertRaisesRegex(RuntimeError, 'support file changed'):
            release.check_sources(self.root)

    def test_import_root_cannot_import_historical_e4(self):
        with (self.root / (release.CURRENT_TARGET + '.lean')).open('a') as f:
            f.write('import QIT.Coding.Private.Superactivation\n')
        with self.assertRaisesRegex(RuntimeError, 'support file changed'):
            release.check_sources(self.root)

    def test_current_target_cannot_be_replaced(self):
        self.manifest['current_target'] = 'WrongTarget'
        (self.root / release.MANIFEST).write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(RuntimeError, 'Unexpected current proof target'):
            release.check_sources(self.root)

    def test_current_closure_cannot_omit_an_imported_source(self):
        del self.manifest['current_target_sources'][next(iter(self.manifest['current_target_sources']))]
        (self.root / release.MANIFEST).write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(RuntimeError, 'source closure'):
            release.check_sources(self.root)

    def test_current_closure_cannot_claim_a_legacy_source_was_built(self):
        name = 'QIT/Coding/Private/Injected.lean'
        self.manifest['current_target_sources'][name] = 'unreviewed'
        (self.root / release.MANIFEST).write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(RuntimeError, 'source closure'):
            release.check_sources(self.root)

    def test_dependency_lockfile_cannot_change(self):
        lake = self.root / 'lake-manifest.json'
        data = json.loads(lake.read_text())
        data['packages'][0]['rev'] = '0' * 40
        lake.write_text(json.dumps(data))
        with self.assertRaisesRegex(RuntimeError, 'support file changed'):
            release.check_sources(self.root)

    def test_unreviewed_historical_file_is_not_ignored(self):
        (self.root / 'QIT/Coding/Private/Superactivation.lean').write_text('axiom bad : False\n')
        with self.assertRaisesRegex(RuntimeError, 'source mismatch'):
            release.check_sources(self.root)


class ReleaseAxiomTests(unittest.TestCase):
    def setUp(self):
        self.manifest = {'current_target_sources': {'QIT/Coding/Private/Example.lean': 'digest'}}
        self.valid = ('LOADED_QIT_MODULE QIT.Coding.Private.Example\n'
                      f'AUDIT {release.ENDPOINT} : '
                      '[propext, Classical.choice, Quot.sound]\n'
                      f'{release.ENDPOINT_MARKER}\n')

    def test_valid_closure_and_axioms(self):
        self.assertIn(release.ENDPOINT, release.validate_axioms(self.valid, self.manifest))

    def test_pretty_printed_multiline_axioms_are_accepted(self):
        output = self.valid.replace('propext, Classical.choice, Quot.sound',
                                    'propext,\n Classical.choice,\n Quot.sound')
        self.assertEqual(release.validate_axioms(output, self.manifest)[release.ENDPOINT],
                         ['propext', 'Classical.choice', 'Quot.sound'])

    def test_hidden_extra_import_is_rejected(self):
        output = self.valid + 'LOADED_QIT_MODULE QIT.Coding.Private.Superactivation\n'
        with self.assertRaisesRegex(RuntimeError, 'source closure'):
            release.validate_axioms(output, self.manifest)

    def test_sorry_in_helper_cannot_pass(self):
        output = self.valid + 'AUDIT QIT.hiddenHelper : [sorryAx]\n'
        with self.assertRaisesRegex(RuntimeError, 'Nonstandard axioms'):
            release.validate_axioms(output, self.manifest)

    def test_missing_literal_endpoint_marker_is_rejected(self):
        output = self.valid.replace(release.ENDPOINT_MARKER, '')
        with self.assertRaisesRegex(RuntimeError, 'Missing literal endpoint'):
            release.validate_axioms(output, self.manifest)

    def test_missing_main_audit_is_rejected(self):
        output = self.valid.replace(release.ENDPOINT, 'QIT.unrelated')
        with self.assertRaisesRegex(RuntimeError, 'Missing literal endpoint'):
            release.validate_axioms(output, self.manifest)

    def test_duplicate_audit_cannot_hide_sorry(self):
        output = (self.valid + 'AUDIT QIT.hiddenHelper : [sorryAx]\n'
                  'AUDIT QIT.hiddenHelper : []\n')
        with self.assertRaisesRegex(RuntimeError, 'Duplicate declaration'):
            release.validate_axioms(output, self.manifest)

    def test_duplicate_standard_audit_is_rejected(self):
        output = self.valid + 'AUDIT ' + release.ENDPOINT + ' : []\n'
        with self.assertRaisesRegex(RuntimeError, 'Duplicate declaration'):
            release.validate_axioms(output, self.manifest)

    def test_malformed_audit_line_is_rejected(self):
        output = self.valid + 'AUDIT QIT.hiddenHelper : [sorryAx\n'
        with self.assertRaisesRegex(RuntimeError, 'Malformed declaration'):
            release.validate_axioms(output, self.manifest)

    def test_success_marker_does_not_override_lean_error(self):
        output = 'Check.lean:6:2: error(lean.unknownIdentifier): Unknown constant\n' + self.valid
        with self.assertRaisesRegex(RuntimeError, 'Lean error'):
            release.validate_axioms(output, self.manifest)


if __name__ == '__main__':
    unittest.main()
