from flask import Blueprint, request, jsonify
from app.services.debugger_service import DebuggerService

debugging_bp = Blueprint('debugging', __name__)
debugger_service = DebuggerService()

@debugging_bp.route('/debug', methods=['POST'])
def debug_code():
    """Debug C/C++ code"""
    try:
        data = request.json
        if not data or 'code' not in data:
            return jsonify({'error': 'No code provided'}), 400
        
        code = data['code']
        filename = data.get('filename', 'temp.c')
        
        result = debugger_service.debug_code(code, filename)
        return jsonify(result), 200
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@debugging_bp.route('/debug/test', methods=['GET'])
def test_debugging():
    """Test debugging integration"""
    try:
        result = debugger_service.test_integration()
        return jsonify(result), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@debugging_bp.route('/debug/status', methods=['GET'])
def debug_status():
    """Get debugging system status"""
    try:
        if debugger_service.debugger is None:
            from modules.module1_debugging.ai_debugger import EnhancedAIDebugger
            debugger_service.debugger = EnhancedAIDebugger()
        
        return jsonify({
            'status': 'ready',
            'chatdbg_available': debugger_service.debugger.chatdbg_available,
            'llmdebugger_available': debugger_service.debugger.llmdebugger_available,
            'gdb_available': debugger_service.debugger.gdb_available
        }), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500