from flask import Blueprint, request, jsonify
from app.services.nlp_service import NLPService

nlp_bp = Blueprint('nlp', __name__)
nlp_service = NLPService()

@nlp_bp.route('/nlp/generate', methods=['POST'])
def generate_tests():
    """Generate test cases from specifications"""
    try:
        data = request.json
        specifications = data.get('specifications', '') if data else ''
        
        result = nlp_service.generate_tests(specifications)
        return jsonify(result), 200
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@nlp_bp.route('/nlp/functions', methods=['GET'])
def get_functions():
    """Get discovered C functions"""
    try:
        result = nlp_service.get_discovered_functions()
        return jsonify(result), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@nlp_bp.route('/nlp/status', methods=['GET'])
def nlp_status():
    """Get NLP system status"""
    try:
        nlp_service.initialize()
        return jsonify({
            'status': 'ready',
            'device': str(nlp_service.generator.device),
            'models_loaded': nlp_service.generator.model is not None,
            'functions_discovered': len(nlp_service.generator.discovered_functions)
        }), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500