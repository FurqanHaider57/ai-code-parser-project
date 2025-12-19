from flask import Blueprint, request, jsonify
from app.services.nlp_service import NLPService

nlp_bp = Blueprint('nlp', __name__)
nlp_service = NLPService()

@nlp_bp.route('/nlp/analyze-code', methods=['POST'])
def analyze_code():
    """
    NEW ENDPOINT: Analyze user-provided C code and generate tests dynamically
    
    Request Body:
    {
        "code": "int factorial(int n) { ... }",
        "filename": "my_code.c"  // optional
    }
    """
    try:
        data = request.json
        
        if not data or 'code' not in data:
            return jsonify({
                'error': 'No code provided',
                'usage': {
                    'endpoint': 'POST /api/nlp/analyze-code',
                    'required_fields': ['code'],
                    'optional_fields': ['filename'],
                    'example': {
                        'code': 'int factorial(int n) { if(n<=1) return 1; return n*factorial(n-1); }',
                        'filename': 'factorial.c'
                    }
                }
            }), 400
        
        code = data['code']
        filename = data.get('filename', 'user_code.c')
        
        # Validate code is not empty
        if not code.strip():
            return jsonify({
                'error': 'Code cannot be empty',
                'status': 'invalid_input'
            }), 400
        
        # Analyze the user's code
        result = nlp_service.analyze_user_code(code, filename)
        
        # Check if there was an error
        if 'error' in result:
            return jsonify(result), 500
        
        return jsonify(result), 200
        
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 500


@nlp_bp.route('/nlp/generate', methods=['POST'])
def generate_tests():
    """
    EXISTING ENDPOINT: Generate test cases from sample code directory
    
    Request Body:
    {
        "specifications": "Optional description"
    }
    """
    try:
        data = request.json
        specifications = data.get('specifications', '') if data else ''
        
        # Call the fixed generate_tests method
        result = nlp_service.generate_tests(specifications)
        
        # Check if there was an error
        if 'error' in result:
            return jsonify(result), 500
        
        return jsonify(result), 200
        
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 500


@nlp_bp.route('/nlp/functions', methods=['GET'])
def get_functions():
    """Get discovered C functions from sample code directory"""
    try:
        result = nlp_service.get_discovered_functions()
        return jsonify(result), 200
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 500


@nlp_bp.route('/nlp/status', methods=['GET'])
def nlp_status():
    """Get NLP system status"""
    try:
        result = nlp_service.get_status()
        return jsonify(result), 200
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 500


@nlp_bp.route('/nlp/quick-test', methods=['POST'])
def quick_test():
    """
    Quick test endpoint - analyze a small code snippet
    
    Request Body:
    {
        "code": "int add(int a, int b) { return a + b; }"
    }
    """
    try:
        data = request.json
        
        if not data or 'code' not in data:
            # Provide a default example if no code provided
            default_code = """
int factorial(int n) {
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}
"""
            data = {'code': default_code}
        
        code = data['code']
        result = nlp_service.analyze_user_code(code, "quick_test.c")
        
        # Return simplified response for quick testing
        if 'error' not in result:
            simplified = {
                'status': result.get('status', 'success'),
                'functions_found': result.get('functions_found', 0),
                'function_names': result.get('discovered_functions', []),
                'total_tests': result.get('total_tests', 0),
                'sample_tests': {}
            }
            
            # Include just the first test from each category for each function
            if 'test_cases' in result:
                for func_name, tests in list(result['test_cases'].items())[:2]:  # First 2 functions
                    simplified['sample_tests'][func_name] = {
                        'boundary_test': tests.get('boundary_tests', [{}])[0].get('description', ''),
                        'normal_test': tests.get('normal_tests', [{}])[0].get('description', ''),
                        'edge_test': tests.get('edge_tests', [{}])[0].get('description', '')
                    }
            
            return jsonify(simplified), 200
        
        return jsonify(result), 500
        
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 500