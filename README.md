# F-Theory: Cosmological Physics

[![Lean 4 CI](https://github.com/Takeo140/F-Theory_Cosmological_Physics/actions/workflows/ci.yml/badge.svg)](https://github.com/Takeo140/F-Theory_Cosmological_Physics/actions)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/1155474552.svg)](https://doi.org/10.5281/zenodo.20693177)

This repository provides a formal **Lean 4** verification of a unified cosmological framework based on the extremal principle of F-theory. 

The framework establishes a rigorous structural correspondence between the two fundamental facets of reality: the **Obverse** (the material/physical manifestation) and the **Reverse** (the underlying mathematical/logical structure). By formalizing this duality, the theory derives cosmic expansion, dark matter, and dark energy as necessary logical consequences of systemic consistency.

---

## ── Core Framework & Axioms

The mathematical foundation is formalized within `Cosmology.lean` and revolves around three primary axioms:

1. **The Extremum Principle**  
   Systems and cosmic fields evolve to extremize (minimize) the governing action functional. The variation of the action $A$ vanishes identically:
   $$\delta A = 0$$

2. **Obverse-Reverse Correspondence**  
   Material reality (Obverse) and logical/mathematical structures (Reverse) are linked via a continuous, structure-preserving mapping:
   $$\Phi: \text{Obverse} \longleftrightarrow \text{Reverse}$$

3. **Logical Consistency**  
   The universe functions as a self-consistent formal system free of internal contradictions. The global logical error functional $C$ is strictly zero:
   $$C = 0$$

---

## ── Key Derivations

Using the foundational axioms, the proofs contained in `Derivations.lean` mathematically derive several key cosmological phenomena:

* **Cosmic Expansion:** Emerges naturally from the dynamic tension and alignment between the Obverse and Reverse spaces.
* **Dark Matter & Dark Energy:** Formulated not as arbitrary physical particles, but as geometric and logical boundary conditions required to preserve global consistency.
* **Mass-Energy Equivalence ($E=mc^2$):** Derived rigorously as a direct consequence of hierarchical consistency and conservation laws within the F-theory framework.

### Relationship to the Four Meta-Axioms
This cosmological system serves as a concrete physical application of the broader **Four Meta-Axioms**. The Extremum Principle instantiates Meta-Axiom 1, while the Obverse-Reverse correspondence serves as a direct manifestation of Meta-Axioms 2 (Topological Space) and 4 (Hierarchical Structure).
* See also: [Meta-Axiom Repository](https://github.com/Takeo140/Meta-Axiom)

---

## ── Repository Structure

```text
├── .github/workflows/    # CI configuration for automated Lean 4 verification
├── Cosmology.lean        # Core definitions, axioms, and the Obverse-Reverse mapping
├── Derivations.lean      # Formal proofs of cosmic expansion, dark energy, and equivalence
├── LICENSE               # Apache License 2.0
└── NOTICE                # Copyright and attribution details
