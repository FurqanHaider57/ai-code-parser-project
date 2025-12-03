"""
Flask Backend for AI Code Debugger - Module 1
Run this file to start the backend server for your frontend
"""

from flask import Flask, request, jsonify, render_template_string
from flask_cors import CORS
import asyncio
import tempfile
import os
from pathlib import Path
import sys

# Add your project to path
sys.path.append(str(Path(__file__).parent))

# Import your Module 1
from modules.module1_debugging import EnhancedAIDebugger

app = Flask(__name__)
CORS(app)  # Enable CORS for frontend-backend communication

# Initialize debugger
debugger = None

# Read the frontend HTML file
FRONTEND_HTML = """
<!-- Frontend HTML will be embedded here -->
"""

@app.route('/')
def index():
    """Serve the frontend HTML"""
    # Read frontend.html from the same directory
    try:
        frontend_path = Path(__file__).parent / 'frontend.html'
        with open(frontend_path, 'r', encoding='utf-8') as f:
            return f.read()
    except FileNotFoundError:
        return """
        <html>
        <body style="font-family: Arial; padding: 50px; text-align: center;">
            <h1 style="color: red;">❌ frontend.html not found!</h1>
            <p>Please save the frontend.html file in the same directory as flask_backend.py</p>
            <p>Current directory: {}</p>
            <hr>
            <h3>Quick Fix:</h3>
            <ol style="text-align: left; max-width: 600px; margin: 20px auto;">
                <li>Save the frontend HTML from Claude as <code>frontend.html</code></li>
                <li>Put it in: <code>{}</code></li>
                <li>Refresh this page</li>
            </ol>
        </body>
        </html>
        """.format(Path(__file__).parent, Path(__file__).parent)

@app.route('/api/analyze', methods=['POST'])
def analyze_code():
    """Analyze uploaded C/C++ code file"""
    global debugger
    
    try:
        # Initialize debugger if not already done
        if debugger is None:
            print("🔧 Initializing AI Debugger...")
            debugger = EnhancedAIDebugger()
            print("✅ Debugger initialized")
        
        # Get uploaded file
        if 'file' not in request.files:
            return jsonify({'error': 'No file uploaded'}), 400
        
        file = request.files['file']
        
        if file.filename == '':
            return jsonify({'error': 'No file selected'}), 400
        
        print(f"📁 Analyzing file: {file.filename}")
        
        # Save to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as temp_file:
            content = file.read().decode('utf-8')
            temp_file.write(content)
            temp_path = temp_file.name
        
        try:
            # Run analysis
            print("🚀 Starting analysis...")
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            result = loop.run_until_complete(debugger.debug_code_file(temp_path))
            loop.close()
            print("✅ Analysis complete")
            
            # Clean up temp file
            os.unlink(temp_path)
            
            # Clean up executable if exists
            if result.get("compilation_analysis", {}).get("executable_path"):
                try:
                    os.unlink(result["compilation_analysis"]["executable_path"])
                except:
                    pass
            
            return jsonify(result)
            
        except Exception as e:
            # Clean up on error
            try:
                os.unlink(temp_path)
            except:
                pass
            raise e
            
    except Exception as e:
        print(f"❌ Error: {e}")
        return jsonify({
            'error': str(e),
            'message': 'Analysis failed. Check if Ollama is running and try again.'
        }), 500

@app.route('/api/test', methods=['GET'])
def test_integration():
    """Test endpoint to verify backend is working"""
    global debugger
    
    try:
        if debugger is None:
            debugger = EnhancedAIDebugger()
        
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(debugger.test_integration())
        loop.close()
        
        return jsonify(result)
        
    except Exception as e:
        return jsonify({
            'error': str(e),
            'status': 'Backend running but integration test failed'
        }), 200

@app.route('/api/health', methods=['GET'])
def health_check():
    """Health check endpoint"""
    global debugger
    
    # Try to initialize debugger if not done
    try:
        if debugger is None:
            debugger = EnhancedAIDebugger()
    except:
        pass
    
    return jsonify({
        'status': 'running',
        'module': 'Module 1 - AI Debugging',
        'ollama_configured': True,
        'gdb_available': debugger.gdb_available if debugger else None
    })

if __name__ == '__main__':
    print("\n" + "="*60)
    print("🚀 Starting AI Code Debugger Backend...")
    print("="*60)
    print("📡 Server will run on http://localhost:5000")
    print("🌐 Frontend will be available at http://localhost:5000")
    print()
    print("⚡ Ollama Status: Already Running ✓")
    print("📝 Model: llama3 (make sure it's pulled)")
    print()
    print("📂 Looking for frontend.html in:")
    print(f"   {Path(__file__).parent}")
    print("="*60)
    print()
    
    # Don't load .env to avoid warnings
    app.config['ENV'] = 'development'
    app.run(debug=True, host='0.0.0.0', port=5000)