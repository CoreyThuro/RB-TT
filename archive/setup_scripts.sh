#!/bin/bash
# scripts/setup.sh - Complete repository setup

echo "Setting up RB-UF-TT Repository..."

# Create directory structure
mkdir -p paper/figures paper/supplementary
mkdir -p src/RBUFTT
mkdir -p examples test docs/{tutorial,theory,api,examples}
mkdir -p notebooks benchmarks tools scripts .github/{workflows,ISSUE_TEMPLATE}
mkdir -p config

# Create lean-toolchain file
echo "leanprover/lean4:v4.3.0" > lean-toolchain

# Create .gitignore
cat > .gitignore << 'EOF'
# Lean build artifacts
build/
lake-packages/
.lake/

# Python
__pycache__/
*.py[cod]
*$py.class
*.so
.Python
env/
venv/
.venv/
.env

# Jupyter Notebook
.ipynb_checkpoints

# LaTeX
*.aux
*.log
*.toc
*.out
*.synctex.gz
*.fdb_latexmk
*.fls

# IDE
.vscode/
.idea/
*.swp
*.swo

# OS
.DS_Store
Thumbs.db
EOF

# Create requirements.txt
cat > requirements.txt << 'EOF'
jupyter>=1.0.0
numpy>=1.21.0
matplotlib>=3.5.0
pandas>=1.3.0
seaborn>=0.11.0
plotly>=5.0.0
ipywidgets>=7.6.0
subprocess32>=3.5.4
pathlib>=1.0.1
EOF

# Create setup.py
cat > setup.py << 'EOF'
from setuptools import setup, find_packages

setup(
    name="rb-uf-tt",
    version="0.1.0",
    description="Resource-Bounded Ultrafinitist Homotopy Type Theory",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    packages=find_packages(),
    install_requires=[
        "jupyter>=1.0.0",
        "numpy>=1.21.0",
        "matplotlib>=3.5.0",
        "pandas>=1.3.0",
        "seaborn>=0.11.0",
    ],
    python_requires=">=3.8",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
    ],
)
EOF

# Create CONTRIBUTING.md
cat > CONTRIBUTING.md << 'EOF'
# Contributing to RB-UF-TT

## Development Setup
1. Install Lean 4 (version 4.3.0 or later)
2. Clone the repository: `git clone https://github.com/username/rb-uf-tt.git`
3. Build the project: `lake build`
4. Install Python dependencies: `pip install -r requirements.txt`
5. Run tests: `lake test`

## Areas of Interest
- Empirical studies of human resource bounds
- New applications of resource-bounded reasoning
- Performance optimizations
- Educational materials and examples
- Documentation improvements

## Code Style
- Follow standard Lean 4 conventions
- Document all public functions
- Include examples in docstrings
- Add tests for new functionality
- Use meaningful variable names

## Submitting Changes
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests if applicable
5. Update documentation
6. Submit a pull request

## Testing
- Run `lake test` for Lean tests
- Run `python -m pytest` for Python tests
- Test notebooks manually in Jupyter

## Documentation
- Update relevant documentation for any changes
- Add examples for new features
- Keep README.md current
EOF

# Create LICENSE
cat > LICENSE << 'EOF'
MIT License

Copyright (c) 2024 RB-UF-TT Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
EOF

# Create build script
cat > scripts/build.sh << 'EOF'
#!/bin/bash
# Build script for RB-UF-TT

echo "Building RB-UF-TT..."

# Build Lean project
echo "Building Lean project..."
lake build

if [ $? -ne 0 ]; then
    echo "Lean build failed!"
    exit 1
fi

# Install Python dependencies
echo "Installing Python dependencies..."
pip install -r requirements.txt

# Build documentation (if doc-gen4 is available)
echo "Building documentation..."
lake build doc-gen4 || echo "doc-gen4 not available, skipping documentation build"

echo "Build complete!"
EOF

chmod +x scripts/build.sh

# Create test script
cat > scripts/test.sh << 'EOF'
#!/bin/bash
# Test script for RB-UF-TT

echo "Running RB-UF-TT tests..."

# Run Lean tests
echo "Running Lean tests..."
lake test

if [ $? -ne 0 ]; then
    echo "Lean tests failed!"
    exit 1
fi

# Run Python tests (if any)
if [ -f "test_python.py" ]; then
    echo "Running Python tests..."
    python -m pytest test_python.py
fi

echo "All tests passed!"
EOF

chmod +x scripts/test.sh

# Create quick start guide
cat > docs/tutorial/getting-started.md << 'EOF'
# Getting Started with RB-UF-TT

## Installation

1. **Install Lean 4**:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Clone the repository**:
   ```bash
   git clone https://github.com/username/rb-uf-tt.git
   cd rb-uf-tt
   ```

3. **Build the project**:
   ```bash
   ./scripts/build.sh
   ```

## Quick Start

### Using Lean directly:
```bash
lake build
lake exe rb-uf-tt
```

### Using Python interface:
```bash
jupyter notebook notebooks/exploration.ipynb
```

## Basic Concepts

- **Resource Contexts**: Every mathematical statement is relative to available resources
- **Feasible Numbers**: Only numbers constructible within resource bounds exist
- **Resource Transfer**: Objects can move between contexts with more resources

## Examples

See the `examples/` directory for detailed examples and the `notebooks/` directory for interactive exploration.
EOF

echo "Repository setup complete!"
echo "Next steps:"
echo "1. Run: lake build"
echo "2. Run: pip install -r requirements.txt"
echo "3. Open: notebooks/exploration.ipynb"