import unittest
from app import create_app

class TestDebuggingEndpoint(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.app = create_app()
        cls.client = cls.app.test_client()

    def test_debugging_endpoint(self):
        response = self.client.get('/api/debugging')
        self.assertEqual(response.status_code, 200)
        self.assertIn('result', response.get_json())

    def test_debugging_with_invalid_data(self):
        response = self.client.post('/api/debugging', json={'invalid': 'data'})
        self.assertEqual(response.status_code, 400)
        self.assertIn('error', response.get_json())

if __name__ == '__main__':
    unittest.main()