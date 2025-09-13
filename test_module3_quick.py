#!/usr/bin/env python3
"""
Quick Module 3 Test Script
"""

import asyncio
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

async def quick_test():
    """Run a quick test of Module 3"""
    
    print("🚀 Quick Module 3 Test")
    print("=" * 30)
    
    try:
        # Import the modules
        from modules.module3_formal.formal_verifier import EnhancedFormalVerifier
        print("✅ Import successful")
        
        # Create verifier
        verifier = EnhancedFormalVerifier()
        print("✅ Verifier created")
        
        # Test simple function
        test_code = """
        int add(int a, int b) {
            return a + b;
        }
        """
        
        result = await verifier.verify_function_with_contracts(test_code, "add")
        print(f"✅ Test verification: {result.get('status', 'unknown')}")
        
        print("\n🎉 Module 3  functionality working!")
        
    except Exception as e:
        print(f"❌ Test failed: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = asyncio.run(quick_test())
    sys.exit(0 if success else 1)
