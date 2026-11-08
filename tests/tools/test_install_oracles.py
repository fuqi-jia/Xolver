#!/usr/bin/env python3
"""Check that oracle transport changes cannot replace the pinned executable."""
import hashlib
import http.client
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
        sleeper = patch.object(installer.time, 'sleep')
        self.sleep = sleeper.start()
        self.addCleanup(sleeper.stop)

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
        with patch.object(installer.urllib.request, 'urlopen', return_value=io.BytesIO(b'{"metadata":true}')) as opened:
            with self.assertRaisesRegex(ValueError, 'checksum mismatch'):
                self.invoke()
        self.assertEqual(opened.call_count, 1)
        self.sleep.assert_not_called()
        self.assertFalse((self.directory / 'cvc5').exists())
        self.assertFalse((self.directory / f'cvc5-{installer.VERSION}.zip').exists())
        self.assertFalse((self.directory / f'cvc5-{installer.VERSION}.download').exists())

    def test_transport_failure_keeps_the_checks_failing(self):
        error = urllib.error.HTTPError(installer.URL, 504, 'Gateway Timeout', {}, None)
        with patch.object(installer.urllib.request, 'urlopen', side_effect=error) as opened:
            with self.assertRaises(urllib.error.HTTPError):
                self.invoke()
        self.assertEqual(opened.call_count, installer.DOWNLOAD_ATTEMPTS)
        self.assertEqual([call.args[0] for call in self.sleep.call_args_list], [1, 2, 4])
        self.assertFalse((self.directory / 'cvc5').exists())

    def test_temporary_gateway_failure_retries_the_same_pinned_asset(self):
        error = urllib.error.HTTPError(installer.URL, 502, 'Bad Gateway', {}, None)
        with patch.object(installer.urllib.request, 'urlopen',
                          side_effect=[error, io.BytesIO(self.archive)]) as opened:
            self.invoke()
        self.assertEqual(opened.call_count, 2)
        self.assertTrue(all(call.args[0].full_url == installer.URL for call in opened.call_args_list))
        self.sleep.assert_called_once_with(1)
        self.assertEqual((self.directory / 'cvc5').read_bytes(), b'synthetic executable fixture')

    def test_interrupted_download_does_not_prefix_the_retry(self):
        class Interrupted(io.BytesIO):
            def read(self, size=-1):
                if self.tell():
                    raise http.client.IncompleteRead(b'partial archive')
                return super().read(8)
        with patch.object(installer.urllib.request, 'urlopen',
                          side_effect=[Interrupted(self.archive), io.BytesIO(self.archive)]) as opened:
            self.invoke()
        self.assertEqual(opened.call_count, 2)
        self.assertEqual((self.directory / f'cvc5-{installer.VERSION}.zip').read_bytes(), self.archive)

    def test_permanent_http_failure_does_not_retry(self):
        error = urllib.error.HTTPError(installer.URL, 404, 'Not Found', {}, None)
        with patch.object(installer.urllib.request, 'urlopen', side_effect=error) as opened:
            with self.assertRaises(urllib.error.HTTPError):
                self.invoke()
        self.assertEqual(opened.call_count, 1)
        self.sleep.assert_not_called()

    def test_retry_still_rejects_a_corrupt_archive(self):
        error = urllib.error.HTTPError(installer.URL, 502, 'Bad Gateway', {}, None)
        with patch.object(installer.urllib.request, 'urlopen',
                          side_effect=[error, io.BytesIO(b'corrupt archive'), io.BytesIO(self.archive)]) as opened:
            with self.assertRaisesRegex(ValueError, 'checksum mismatch'):
                self.invoke()
        self.assertEqual(opened.call_count, 2)
        self.assertFalse((self.directory / 'cvc5').exists())


if __name__ == '__main__':
    unittest.main()
