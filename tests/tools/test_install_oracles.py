#!/usr/bin/env python3
"""Check that oracle transport changes cannot replace the pinned executable."""
import hashlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import urllib.error
import zipfile

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('install_oracles', ROOT / 'tools/ci/install_oracles.py')
installer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(installer)


class OracleInstallTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        content = io.BytesIO()
        with zipfile.ZipFile(content, 'w') as archive:
            archive.writestr('fixture/bin/cvc5', b'synthetic executable fixture')
            archive.writestr('fixture/licenses/COPYING', b'synthetic license fixture')
        self.archive = content.getvalue()
        self.digest = hashlib.sha256(self.archive).hexdigest()

    def invoke(self):
        with patch.object(sys, 'argv', ['install_oracles.py', str(self.directory)]), \
             patch.object(installer, 'SHA256', self.digest), patch('builtins.print'):
            installer.main()

    def test_official_asset_download_is_verified_and_extracted(self):
        with patch.object(installer.urllib.request, 'urlopen', return_value=io.BytesIO(self.archive)) as opened:
            self.invoke()
        request = opened.call_args.args[0]
        self.assertEqual(request.full_url, installer.URL)
        self.assertEqual(request.get_header('Accept'), 'application/octet-stream')
        self.assertEqual(opened.call_args.kwargs['timeout'], 60)
        target = self.directory / 'cvc5'
        self.assertEqual(target.read_bytes(), b'synthetic executable fixture')
        self.assertEqual(target.stat().st_mode & 0o777, 0o755)
        self.assertEqual((self.directory / 'licenses/COPYING').read_bytes(), b'synthetic license fixture')

    def test_verified_cache_requires_no_network(self):
        (self.directory / f'cvc5-{installer.VERSION}.zip').write_bytes(self.archive)
        with patch.object(installer.urllib.request, 'urlopen', side_effect=AssertionError('unexpected network')):
            self.invoke()
        self.assertEqual((self.directory / 'cvc5').read_bytes(), b'synthetic executable fixture')

    def test_metadata_or_corrupt_response_cannot_be_installed(self):
        with patch.object(installer.urllib.request, 'urlopen', return_value=io.BytesIO(b'{"metadata":true}')):
            with self.assertRaisesRegex(ValueError, 'checksum mismatch'):
                self.invoke()
        self.assertFalse((self.directory / 'cvc5').exists())
        self.assertFalse((self.directory / f'cvc5-{installer.VERSION}.zip').exists())

    def test_transport_failure_keeps_the_checks_failing(self):
        error = urllib.error.HTTPError(installer.URL, 504, 'Gateway Timeout', {}, None)
        with patch.object(installer.urllib.request, 'urlopen', side_effect=error):
            with self.assertRaises(urllib.error.HTTPError):
                self.invoke()
        self.assertFalse((self.directory / 'cvc5').exists())


if __name__ == '__main__':
    unittest.main()
