from flask import Blueprint, request, jsonify
from app.services.formal_service import FormalService

formal_bp = Blueprint('formal', __name__)
formal_service = FormalService()

@formal_bp.route('/formal/verify', methods=['POST'])
def verify_code():
    """Verify C code with formal methods"""
    try:
        data = request.json
        if not data or 'code' not in data:
            return jsonify({'error': 'No code provided'}), 400
        
        code = data['code']
        function_name = data.get('function_name', '')
        
        result = formal_service.verify_code(code, function_name)
        return jsonify(result), 200
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@formal_bp.route('/formal/test', methods=['GET'])
def test_formal():
    """Test formal verification integration"""
    try:
        result = formal_service.test_integration()
        return jsonify(result), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@formal_bp.route('/formal/status', methods=['GET'])
def formal_status():
    """Get formal verification system status"""
    try:
        result = formal_service.check_status()
        return jsonify(result), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500