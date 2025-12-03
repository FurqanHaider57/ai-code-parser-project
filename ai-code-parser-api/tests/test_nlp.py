import pytest
from app import create_app

@pytest.fixture
def client():
    app = create_app()
    with app.test_client() as client:
        yield client

def test_nlp_endpoint(client):
    response = client.get('/nlp')
    assert response.status_code == 200
    assert 'result' in response.get_json()

def test_nlp_with_invalid_data(client):
    response = client.post('/nlp', json={'invalid': 'data'})
    assert response.status_code == 400
    assert 'error' in response.get_json()