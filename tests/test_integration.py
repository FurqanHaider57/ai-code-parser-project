"""
Integration Tests
"""
import pytest # type: ignore
import sys
from pathlib import Path
import logging

# Suppress logging during tests
logging.disable(logging.CRITICAL)

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.append(str(project_root))

from main import AICodeParser

class TestPhase1Integration:
    """Test Phase 1-2 integration functionality"""
    
    def test_ai_code_parser_initialization(self):
        """Test that the main application initializes correctly"""
        app = AICodeParser()
        assert app is not None
        assert hasattr(app, 'debugger')
        assert hasattr(app, 'test_generator')
        assert hasattr(app, 'formal_verifier')
        assert hasattr(app, 'simulink_generator')
    
    def test_module1_debugging(self):
        """Test Module 1 debugging integration"""
        from modules.module1_debugging import AIDebugger
        debugger = AIDebugger()
        result = debugger.test_integration()
        
        assert result is not None
        assert 'status' in result
        assert 'chatdbg_ready' in result
        assert 'llmdebugger_ready' in result
        assert result['status'] == "Phase 1-2 - Basic integration complete"
    
    def test_module2_nlp(self):
        """Test Module 2 NLP integration"""
        from modules.module2_nlp import NLPTestGenerator
        generator = NLPTestGenerator()
        result = generator.test_basic_functionality()
        
        assert result is not None
        assert 'status' in result
        assert 'test_cases' in result
        assert len(result['test_cases']) > 0
        assert result['status'] == "Phase 1-2 - Basic NLP setup complete"
    
    def test_module3_formal(self):
        """Test Module 3 formal verification integration"""
        from modules.module3_formal import FormalVerifier
        verifier = FormalVerifier()
        result = verifier.test_framac_integration()
        
        assert result is not None
        assert 'status' in result
        assert 'contracts' in result
        assert 'framac_available' in result
        assert result['status'] == "Phase 1-2 - Basic Frama-C integration complete"
    
    def test_module4_simulink(self):
        """Test Module 4 Simulink integration"""
        from modules.module4_simulink import SimulinkGenerator
        generator = SimulinkGenerator()
        result = generator.test_basic_parsing()
        
        assert result is not None
        assert 'status' in result
        assert 'parsed_functions' in result
        assert 'simulink_blocks' in result
        assert result['status'] == "Phase 1-2 - Basic parsing and template generation complete"
    
    def test_full_integration_demo(self):
        """Test the full integration demo"""
        app = AICodeParser()
        results = app.run_phase1_demo()
        
        assert results is not None
        assert 'module1' in results
        assert 'module2' in results
        assert 'module3' in results
        assert 'module4' in results
        
        # Verify each module returned valid results
        for module_key, module_result in results.items():
            assert isinstance(module_result, dict)
            assert 'status' in module_result

if __name__ == "__main__":
    # Run tests directly
    pytest.main([__file__, "-v"])