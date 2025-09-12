"""
Simulink Model Generator from C/C++ code
"""
import logging
import re
from pathlib import Path
import subprocess

logger = logging.getLogger(__name__)

class SimulinkGenerator:
    """Generate Simulink models from C/C++ code"""
    
    def __init__(self):
        logger.info("Initializing Simulink Generator")
        self.clang_available = self._check_clang_installation()
        self.matlab_available = self._check_matlab_availability()
    
    def _check_clang_installation(self):
        """Check if Clang is properly installed"""
        try:
            result = subprocess.run(["clang", "--version"], 
                                  capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                logger.info("Clang found and available")
                return True
            else:
                logger.warning("Clang not working properly")
                return False
        except Exception as e:
            logger.error(f"Clang check failed: {e}")
            return False
    
    def _check_matlab_availability(self):
        """Check if MATLAB is available (optional for Phase 1-2)"""
        try:
            result = subprocess.run(["matlab", "-batch", "disp('MATLAB available')"], 
                                  capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                logger.info("MATLAB found and available")
                return True
            else:
                logger.info("MATLAB not available (will use simulation mode)")
                return False
        except Exception as e:
            logger.info("MATLAB not available (will use simulation mode)")
            return False
    
    def parse_c_function(self, c_code: str):
        """Parse C function for Simulink conversion"""
        logger.info("Parsing C function for Simulink conversion")
        
        # Phase 1-2: Basic regex-based parsing
        function_info = {
            "functions": [],
            "variables": [],
            "operations": [],
            "status": "Basic C parsing setup complete"
        }
        
        # Extract function signatures
        func_pattern = r'(\w+)\s+(\w+)\s*\(([^)]*)\)'
        functions = re.findall(func_pattern, c_code)
        
        for return_type, func_name, params in functions:
            function_info["functions"].append({
                "name": func_name,
                "return_type": return_type,
                "parameters": [p.strip() for p in params.split(',') if p.strip()],
                "simulink_compatible": self._assess_simulink_compatibility(c_code)
            })
        
        # Extract variables
        var_pattern = r'(\w+)\s+(\w+)\s*[;=]'
        variables = re.findall(var_pattern, c_code)
        for var_type, var_name in variables:
            if var_type in ['int', 'float', 'double']:
                function_info["variables"].append({
                    "name": var_name,
                    "type": var_type,
                    "simulink_type": self._map_to_simulink_type(var_type)
                })
        
        return function_info
    
    def _assess_simulink_compatibility(self, c_code: str):
        """Assess if C code is compatible with Simulink conversion"""
        # Check for DSP/control system indicators
        dsp_indicators = ['filter', 'fft', 'signal', 'control', 'pid', 'gain']
        math_indicators = ['sin', 'cos', 'sqrt', 'pow', 'log']
        
        code_lower = c_code.lower()
        compatibility_score = 0
        
        for indicator in dsp_indicators + math_indicators:
            if indicator in code_lower:
                compatibility_score += 1
        
        return {
            "compatible": compatibility_score > 0,
            "score": compatibility_score,
            "reasons": f"Found {compatibility_score} DSP/math indicators"
        }
    
    def _map_to_simulink_type(self, c_type: str):
        """Map C types to Simulink types"""
        type_mapping = {
            'int': 'int32',
            'float': 'single',
            'double': 'double',
            'char': 'uint8'
        }
        return type_mapping.get(c_type, 'double')
    
    def generate_simulink_model_template(self, function_info: dict):
        """Generate Simulink model template"""
        logger.info("Generating Simulink model template")
        
        template = {
            "model_name": f"Generated_Model_{function_info['functions'][0]['name'] if function_info['functions'] else 'Unknown'}",
            "blocks": [],
            "connections": [],
            "matlab_available": self.matlab_available,
            "status": "Basic template generation"
        }
        
        # Generate basic blocks for each function
        for func in function_info["functions"]:
            template["blocks"].append({
                "type": "Subsystem",
                "name": func["name"],
                "inputs": len(func["parameters"]),
                "outputs": 1 if func["return_type"] != "void" else 0,
                "implementation": "C Function Block"
            })
        
        return template
    
    def test_basic_parsing(self):
        """Test basic C parsing functionality"""
        logger.info("Testing basic C parsing")
        
        sample_c_code = """
float pid_controller(float setpoint, float measurement, float kp, float ki, float kd) {
    static float integral = 0.0;
    static float previous_error = 0.0;
    
    float error = setpoint - measurement;
    integral += error;
    float derivative = error - previous_error;
    
    float output = kp * error + ki * integral + kd * derivative;
    previous_error = error;
    
    return output;
}

int main() {
    float result = pid_controller(100.0, 95.0, 0.1, 0.01, 0.05);
    return 0;
}
"""
        
        function_info = self.parse_c_function(sample_c_code)
        simulink_template = self.generate_simulink_model_template(function_info)
        
        result = {
            "parsed_functions": len(function_info["functions"]),
            "simulink_blocks": len(simulink_template["blocks"]),
            "clang_available": self.clang_available,
            "matlab_available": self.matlab_available,
            "function_info": function_info,
            "simulink_template": simulink_template,
            "status": "Phase 1-2 - Basic parsing and template generation complete"
        }
        
        logger.info(f"Simulink generator test result: {result['status']}")
        return result