import pytest
from app import create_app

@pytest.fixture
def client():
    app = create_app()
    with app.test_client() as client:
        yield client

def test_formal_endpoint(client):
    response = client.get('/api/formal')
    assert response.status_code == 200
    assert 'result' in response.get_json()  # Adjust based on actual response structure

def test_formal_with_invalid_data(client):
    response = client.post('/api/formal', json={'invalid': 'data'})
    assert response.status_code == 400  # Adjust based on expected error handling
    assert 'error' in response.get_json()  # Adjust based on actual response structure