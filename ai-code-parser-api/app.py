import sys
from pathlib import Path
from flask import Flask, jsonify
from flask_cors import CORS

# Add parent directory to path to access modules
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

# Add current directory to path for config
app_root = Path(__file__).parent
sys.path.insert(0, str(app_root))

from app.routes.debugging import debugging_bp
from app.routes.nlp import nlp_bp
from app.routes.formal import formal_bp

def create_app():
    app = Flask(__name__)
    CORS(app)  # Enable CORS for cross-origin requests
    
    # Load configuration directly instead of using from_object
    app.config['DEBUG'] = True
    app.config['TESTING'] = False
    app.config['SECRET_KEY'] = 'dev-secret-key-change-in-production'
    app.config['JSON_SORT_KEYS'] = False
    app.config['API_VERSION'] = 'v1'

    # Register blueprints with URL prefixes
    app.register_blueprint(debugging_bp, url_prefix='/api')
    app.register_blueprint(nlp_bp, url_prefix='/api')
    app.register_blueprint(formal_bp, url_prefix='/api')
    
    # Health check endpoint
    @app.route('/health', methods=['GET'])
    def health():
        return jsonify({
            'status': 'running',
            'message': 'AI Code Parser API is healthy',
            'version': app.config['API_VERSION']
        })
    
    # Root endpoint
    @app.route('/', methods=['GET'])
    def index():
        return jsonify({
            'message': 'AI Code Parser API',
            'version': app.config['API_VERSION'],
            'endpoints': {
                'debugging': {
                    'debug': 'POST /api/debug',
                    'status': 'GET /api/debug/status',
                    'test': 'GET /api/debug/test'
                },
                'nlp': {
                    'generate': 'POST /api/nlp/generate',
                    'functions': 'GET /api/nlp/functions',
                    'status': 'GET /api/nlp/status'
                },
                'formal': {
                    'verify': 'POST /api/formal/verify',
                    'status': 'GET /api/formal/status',
                    'test': 'GET /api/formal/test'
                }
            }
        })

    return app

if __name__ == "__main__":
    app = create_app()
    print("🚀 Starting AI Code Parser API")
    print("=" * 60)
    print("📡 Server running on http://localhost:5000")
    print("🏥 Health check: http://localhost:5000/health")
    print("")
    print("📚 Available Endpoints:")
    print("  🔧 Module 1 (Debugging):")
    print("     POST /api/debug - Debug C/C++ code")
    print("     GET  /api/debug/status - Check debugger status")
    print("     GET  /api/debug/test - Test integration")
    print("")
    print("  🧠 Module 2 (NLP Test Generation):")
    print("     POST /api/nlp/generate - Generate test cases")
    print("     GET  /api/nlp/functions - List discovered functions")
    print("     GET  /api/nlp/status - Check NLP status")
    print("")
    print("  ✅ Module 3 (Formal Verification):")
    print("     POST /api/formal/verify - Verify code with ACSL")
    print("     GET  /api/formal/status - Check verifier status")
    print("     GET  /api/formal/test - Test integration")
    print("=" * 60)
    app.run(debug=True, host='0.0.0.0', port=5000)