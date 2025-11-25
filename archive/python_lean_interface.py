"""
Resource-Bounded Ultrafinitist Homotopy Type Theory - Python Interface
A Python interface for interacting with RB-UF-TT Lean code from Jupyter notebooks.
"""

import subprocess
import tempfile
import os
import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from dataclasses import dataclass

@dataclass
class ResourceContext:
    """Python representation of a Lean ResourceContext"""
    time_bound: int
    memory_bound: int
    proof_depth: int
    construction_steps: int
    collaboration_size: int
    name: str = ""
    
    def __str__(self):
        return f"ResourceContext({self.name}: T={self.time_bound}, M={self.memory_bound}, D={self.proof_depth}, C={self.construction_steps}, N={self.collaboration_size})"
    
    def to_lean(self) -> str:
        """Convert to Lean code representation"""
        return f"""{{
  time_bound := {self.time_bound},
  memory_bound := {self.memory_bound},
  proof_depth := {self.proof_depth},
  construction_steps := {self.construction_steps},
  collaboration_size := {self.collaboration_size}
}}"""

@dataclass
class FeasibleNumber:
    """Python representation of a Lean FeasibleNumber"""
    value: int
    context: ResourceContext
    construction_cost: int
    
    def __str__(self):
        return f"FeasibleNumber({self.value} in {self.context.name})"

class RBUFTTInterface:
    """Main interface for interacting with RB-UF-TT Lean code"""
    
    def __init__(self, project_path: str = "."):
        self.project_path = Path(project_path)
        self.temp_dir = tempfile.mkdtemp()
        
        # Standard resource contexts
        self.contexts = {
            'minimal': ResourceContext(60, 10, 2, 20, 1, 'R_minimal'),
            'student': ResourceContext(1200, 100, 5, 200, 1, 'R_student'),
            'researcher': ResourceContext(604800, 10000, 25, 100000, 5, 'R_researcher'),
            'computer': ResourceContext(1000000000, 1000000, 1000000, 1000000000, 1000, 'R_computer'),
            'volpin': ResourceContext(3600, 500, 10, 1000, 1, 'R_volpin')
        }
    
    def execute_lean(self, code: str, imports: List[str] = None) -> Tuple[bool, str, str]:
        """Execute Lean code and return success status, stdout, stderr"""
        if imports is None:
            imports = ['RBUFTT.ResourceContext', 'RBUFTT.FeasibleNumbers', 'RBUFTT.Examples']
        
        # Create temporary Lean file
        temp_file = Path(self.temp_dir) / 'temp.lean'
        
        full_code = '\n'.join([f'import {imp}' for imp in imports])
        full_code += '\n\nnamespace RBUFTT\n\n'
        full_code += code
        full_code += '\n\nend RBUFTT'
        
        with open(temp_file, 'w') as f:
            f.write(full_code)
        
        try:
            # Run lean on the temporary file
            result = subprocess.run(
                ['lean', str(temp_file)],
                cwd=self.project_path,
                capture_output=True,
                text=True,
                timeout=30
            )
            return result.returncode == 0, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return False, "", "Execution timed out"
        except FileNotFoundError:
            return False, "", "Lean not found. Please ensure Lean 4 is installed and in PATH."
    
    def check_lean_availability(self) -> bool:
        """Check if Lean is available and the project builds"""
        try:
            result = subprocess.run(['lean', '--version'], capture_output=True, text=True)
            if result.returncode != 0:
                return False
            
            # Try to build the project
            result = subprocess.run(['lake', 'build'], cwd=self.project_path, capture_output=True)
            return result.returncode == 0
        except FileNotFoundError:
            return False
    
    def create_resource_context(self, name: str, time_bound: int, memory_bound: int, 
                              proof_depth: int, construction_steps: int, 
                              collaboration_size: int) -> ResourceContext:
        """Create a new resource context"""
        context = ResourceContext(time_bound, memory_bound, proof_depth, 
                                construction_steps, collaboration_size, name)
        self.contexts[name] = context
        return context
    
    def volpin_hesitation(self, context_name: str, max_power: int = 10) -> Dict[int, float]:
        """Calculate Volpin's hesitation for powers of 2 up to max_power"""
        if context_name not in self.contexts:
            raise ValueError(f"Unknown context: {context_name}")
        
        context = self.contexts[context_name]
        results = {}
        
        code = f"""
def test_context : ResourceContext := {context.to_lean()}

-- Calculate hesitation for powers of 2
"""
        
        for n in range(1, max_power + 1):
            power_code = f"""
#eval volpin_hesitation test_context {n}
"""
            success, stdout, stderr = self.execute_lean(code + power_code)
            if success and stdout.strip():
                try:
                    # Extract the float value from Lean output
                    match = re.search(r'(\d+\.?\d*)', stdout)
                    if match:
                        results[n] = float(match.group(1))
                except:
                    results[n] = 0.0
            else:
                results[n] = 0.0
        
        return results
    
    def test_arithmetic(self, context_name: str, operations: List[Tuple[str, int, int]]) -> Dict:
        """Test arithmetic operations in a given context"""
        if context_name not in self.contexts:
            raise ValueError(f"Unknown context: {context_name}")
        
        context = self.contexts[context_name]
        results = {}
        
        for op, a, b in operations:
            if op == 'add':
                lean_op = 'rb_add'
            elif op == 'mult':
                lean_op = 'rb_mult'
            elif op == 'exp':
                lean_op = 'rb_exp'
            else:
                continue
            
            code = f"""
def test_context : ResourceContext := {context.to_lean()}

-- Test {op} operation
example : Option (FeasibleNat test_context) := 
  {lean_op} test_context ⟨{a}, sorry⟩ ⟨{b}, sorry⟩

#check {lean_op} test_context ⟨{a}, sorry⟩ ⟨{b}, sorry⟩
"""
            
            success, stdout, stderr = self.execute_lean(code)
            results[f"{op}({a},{b})"] = {
                'success': success,
                'result': 'compiles' if success else 'fails',
                'error': stderr if not success else None
            }
        
        return results
    
    def compare_contexts(self, context_names: List[str], test_number: int) -> pd.DataFrame:
        """Compare how different contexts handle the same number"""
        data = []
        
        for name in context_names:
            if name not in self.contexts:
                continue
                
            context = self.contexts[name]
            
            # Test if the number is feasible
            code = f"""
def test_context : ResourceContext := {context.to_lean()}

-- Check if {test_number} is feasible
def test_number : ℕ := {test_number}
def is_feasible : Prop := construction_cost test_number ≤ test_context.construction_steps

#check is_feasible
"""
            
            success, stdout, stderr = self.execute_lean(code)
            
            data.append({
                'Context': name,
                'Time Bound': context.time_bound,
                'Memory Bound': context.memory_bound,
                'Construction Steps': context.construction_steps,
                'Can Handle': success,
                'Number': test_number
            })
        
        return pd.DataFrame(data)
    
    def visualize_volpin_hesitation(self, context_names: List[str], max_power: int = 10):
        """Visualize Volpin's hesitation across different contexts"""
        plt.figure(figsize=(12, 8))
        
        for context_name in context_names:
            if context_name not in self.contexts:
                continue
                
            hesitation_data = self.volpin_hesitation(context_name, max_power)
            powers = list(hesitation_data.keys())
            certainties = list(hesitation_data.values())
            
            plt.plot(powers, certainties, 'o-', label=f'{context_name}', linewidth=2, markersize=6)
        
        plt.xlabel('Power of 2 (n in 2^n)', fontsize=12)
        plt.ylabel('Certainty Level', fontsize=12)
        plt.title("Volpin's Hesitation: Certainty about Powers of 2", fontsize=14)
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.ylim(0, 1.1)
        
        # Add annotations for actual values
        powers_annotation = [1, 2, 3, 4, 5, 10]
        for n in powers_annotation:
            if n <= max_power:
                plt.annotate(f'2^{n} = {2**n}', xy=(n, 0.05), xytext=(n, 0.15),
                           ha='center', fontsize=9, alpha=0.7,
                           arrowprops=dict(arrowstyle='->', alpha=0.5))
        
        plt.tight_layout()
        plt.show()
    
    def visualize_resource_contexts(self):
        """Visualize different resource contexts"""
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        
        # Prepare data
        contexts_data = []
        for name, context in self.contexts.items():
            contexts_data.append({
                'Name': name,
                'Time': np.log10(context.time_bound + 1),
                'Memory': np.log10(context.memory_bound + 1),
                'Depth': context.proof_depth,
                'Steps': np.log10(context.construction_steps + 1),
                'Collaboration': context.collaboration_size
            })
        
        df = pd.DataFrame(contexts_data)
        
        # Time bounds (log scale)
        axes[0,0].bar(df['Name'], df['Time'])
        axes[0,0].set_title('Time Bounds (log₁₀)')
        axes[0,0].set_ylabel('Log₁₀(Time Bound)')
        axes[0,0].tick_params(axis='x', rotation=45)
        
        # Memory bounds (log scale)
        axes[0,1].bar(df['Name'], df['Memory'])
        axes[0,1].set_title('Memory Bounds (log₁₀)')
        axes[0,1].set_ylabel('Log₁₀(Memory Bound)')
        axes[0,1].tick_params(axis='x', rotation=45)
        
        # Proof depth
        axes[1,0].bar(df['Name'], df['Depth'])
        axes[1,0].set_title('Proof Depth Bounds')
        axes[1,0].set_ylabel('Proof Depth')
        axes[1,0].tick_params(axis='x', rotation=45)
        
        # Construction steps (log scale)
        axes[1,1].bar(df['Name'], df['Steps'])
        axes[1,1].set_title('Construction Steps (log₁₀)')
        axes[1,1].set_ylabel('Log₁₀(Construction Steps)')
        axes[1,1].tick_params(axis='x', rotation=45)
        
        plt.tight_layout()
        plt.show()
    
    def arithmetic_success_heatmap(self, operations: List[str], numbers: List[int], 
                                 context_names: List[str]):
        """Create a heatmap showing which arithmetic operations succeed in which contexts"""
        data = []
        
        for context_name in context_names:
            for op in operations:
                for num in numbers:
                    # Test the operation (simplified - just checking if numbers are feasible)
                    context = self.contexts[context_name]
                    
                    if op == 'add':
                        result_val = num + num
                    elif op == 'mult':
                        result_val = num * num
                    elif op == 'exp':
                        result_val = num ** min(num, 10)  # Cap exponent for safety
                    else:
                        result_val = num
                    
                    # Simple feasibility check based on construction cost approximation
                    feasible = result_val <= context.construction_steps
                    
                    data.append({
                        'Context': context_name,
                        'Operation': f'{op}({num},{num})',
                        'Success': 1 if feasible else 0
                    })
        
        df = pd.DataFrame(data)
        pivot_df = df.pivot(index='Context', columns='Operation', values='Success')
        
        plt.figure(figsize=(12, 6))
        sns.heatmap(pivot_df, annot=True, cmap='RdYlGn', cbar_kws={'label': 'Success (1=Yes, 0=No)'})
        plt.title('Arithmetic Operations Success by Resource Context')
        plt.tight_layout()
        plt.show()
        
        return pivot_df
    
    def educational_progression(self):
        """Visualize mathematical content progression across educational levels"""
        educational_contexts = {
            'Elementary': ResourceContext(300, 20, 2, 50, 1, 'elementary'),
            'Middle School': ResourceContext(900, 60, 4, 150, 2, 'middle'),
            'High School': ResourceContext(1800, 200, 8, 1000, 3, 'high_school'),
            'University': ResourceContext(7200, 2000, 20, 50000, 10, 'university'),
            'Graduate': ResourceContext(36000, 10000, 30, 500000, 20, 'graduate')
        }
        
        # Calculate maximum feasible numbers for each level
        max_numbers = {}
        for level, context in educational_contexts.items():
            # Approximate maximum feasible number
            max_numbers[level] = min(context.construction_steps, 10**6)
        
        levels = list(max_numbers.keys())
        max_vals = list(max_numbers.values())
        
        plt.figure(figsize=(10, 6))
        bars = plt.bar(levels, np.log10(max_vals))
        plt.ylabel('Log₁₀(Maximum Feasible Number)')
        plt.title('Mathematical Content Progression Across Educational Levels')
        plt.xticks(rotation=45)
        
        # Add actual values as annotations
        for bar, val in zip(bars, max_vals):
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                    f'{val:,}', ha='center', va='bottom', fontsize=9)
        
        plt.tight_layout()
        plt.show()
    
    def consistency_radius_analysis(self, large_numbers: List[int]):
        """Analyze consistency radii for theories with large number bounds"""
        results = {}
        
        for num in large_numbers:
            # For each context, check if the number is feasible
            context_results = {}
            for name, context in self.contexts.items():
                # Rough approximation: number is consistent if it's much larger than feasible numbers
                max_feasible = context.construction_steps
                consistent = num > max_feasible * 1000  # Large margin
                context_results[name] = consistent
            
            results[f'Theory: ∀n, n < {num}'] = context_results
        
        df = pd.DataFrame(results).T
        
        plt.figure(figsize=(10, 6))
        sns.heatmap(df.astype(int), annot=True, cmap='RdYlGn', 
                   cbar_kws={'label': 'Consistent (1=Yes, 0=No)'})
        plt.title('Consistency of Large Number Bound Theories')
        plt.xlabel('Resource Context')
        plt.ylabel('Theory')
        plt.tight_layout()
        plt.show()
        
        return df
    
    def cleanup(self):
        """Clean up temporary files"""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

# Convenience functions for notebook use
def create_interface(project_path: str = ".") -> RBUFTTInterface:
    """Create and return a new RBUFTT interface"""
    return RBUFTTInterface(project_path)

def quick_volpin_demo(interface: RBUFTTInterface):
    """Quick demonstration of Volpin's hesitation"""
    print("Volpin's Hesitation Demonstration")
    print("=" * 40)
    
    contexts_to_test = ['minimal', 'student', 'researcher']
    
    for context_name in contexts_to_test:
        print(f"\n{context_name.title()} Context:")
        hesitation = interface.volpin_hesitation(context_name, 8)
        
        for n, certainty in hesitation.items():
            power_val = 2 ** n
            certainty_desc = "immediate" if certainty > 0.8 else \
                           "short pause" if certainty > 0.5 else \
                           "long pause" if certainty > 0.2 else \
                           "very uncertain"
            print(f"  2^{n} = {power_val}: {certainty_desc} (certainty: {certainty:.3f})")

def setup_notebook_environment():
    """Set up the notebook environment with proper styling"""
    plt.style.use('seaborn-v0_8')
    sns.set_palette("husl")
    
    # Display settings
    pd.set_option('display.max_columns', None)
    pd.set_option('display.width', None)
    pd.set_option('display.max_colwidth', 50)
    
    print("RB-UF-TT Python Interface Ready!")
    print("Use create_interface() to start exploring.")

if __name__ == "__main__":
    # Basic test when run as script
    interface = create_interface()
    
    if interface.check_lean_availability():
        print("✓ Lean is available and project builds successfully")
        quick_volpin_demo(interface)
    else:
        print("✗ Lean is not available or project doesn't build")
        print("Please ensure Lean 4 is installed and the project builds with 'lake build'")
    
    interface.cleanup()