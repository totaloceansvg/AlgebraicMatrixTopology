"""
Copyright (c) 2026 HaiTao Zhao. All rights reserved.
Author: HaiTao Zhao
Title: Matrix-Native Discrete Evolution & Dynamic Projection Engine (RMQM-Engine)
Description: Python companion script for the Lean 4 MatrixTopologyCore module.
             Executes discrete matrix evolution, detects singularity and rank collapse,
             and dynamically generates idempotent projection operators (P^2 = P) for subspace closure.
"""

import numpy as np

class MatrixEvolutionEngine:
    def __init__(self, initial_matrix, evolution_func):
        """
        Initializes the discrete matrix evolution engine.
        :param initial_matrix: Starting matrix X_0 (numpy array)
        :param evolution_func: A function M(X) returning the state-dependent evolution matrix
        """
        self.X = np.array(initial_matrix, dtype=float)
        self.evolution_func = evolution_func
        self.history_states = [self.X.copy()]
        self.projector_history = []
        self.rank_history = []

    def generate_idempotent_projector(self, matrix, tol=1e-5):
        """
        Generates a dynamic idempotent projection operator P (P^2 = P) 
        using Singular Value Decomposition (SVD) to isolate the stable subspace 
        from a collapsed or singular state.
        """
        U, s, Vt = np.linalg.svd(matrix)
        # Identify valid dimensions above numerical tolerance (stable subspace)
        active_dims = np.sum(s > tol)
        if active_dims == 0:
            active_dims = 1  # Fallback to prevent total annihilation

        # Construct projection matrix P = U_r * U_r^T
        # This structurally guarantees P^2 = P (Idempotency)
        U_r = U[:, :active_dims]
        P = U_r @ U_r.T
        return P

    def step(self):
        """
        Executes a single discrete evolution step:
        X_{n+1} = M(X_n) * X_n
        Triggers singularity check and dynamic projection closure when rank drops.
        """
        # 1. Compute state-dependent evolution matrix M(X)
        M = self.evolution_func(self.X)
        
        # 2. Pure discrete matrix multiplication chain (bypassing continuous differential equations)
        X_next = M @ self.X

        # 3. Check for rank collapse or determinant vanishing (matrix-level 0/0 or singularity)
        max_rank = X_next.shape[0]
        current_rank = np.linalg.matrix_rank(X_next)
        det_val = np.linalg.det(X_next) if X_next.shape[0] == X_next.shape[1] else 1.0
        
        self.rank_history.append(current_rank)

        # 4. Crisis handling: When singularity/collapse occurs, trigger dynamic projection (P^2 = P)
        if current_rank < max_rank or np.abs(det_val) < 1e-7:
            # Generate dynamic projector P
            P = self.generate_idempotent_projector(X_next)
            
            # --- Machine Validation of Idempotency (matches Lean 4 'IsProjection') ---
            is_idempotent = np.allclose(P @ P, P, atol=1e-7)
            assert is_idempotent, "Runtime Error: Generated projector violates P^2 = P!"
            
            # Also verify complementary projection property (1 - P)
            I = np.eye(max_rank)
            comp_P = I - P
            is_comp_idempotent = np.allclose(comp_P @ comp_P, comp_P, atol=1e-7)
            assert is_comp_idempotent, "Runtime Error: Complementary projector violates (1-P)^2 = (1-P)!"

            # Apply subspace projection closure: State is safely locked into the valid subspace
            X_next = P @ X_next @ P
            self.projector_history.append(P)

        self.X = X_next
        self.history_states.append(self.X.copy())
        return self.X

    def run_simulation(self, steps=10):
        """Runs the discrete matrix evolution for a given number of steps."""
        print(f"--- Starting Matrix Evolution Simulation ({steps} steps) ---")
        for i in range(steps):
            prev_rank = np.linalg.matrix_rank(self.X)
            self.step()
            print(f"Step {i+1}: Rank = {np.linalg.matrix_rank(self.X)} | State norm = {np.linalg.norm(self.X):.4f}")
        print("--- Simulation Completed Successfully ---")


# ==========================================
# Example Execution & Verification Test
# ==========================================
if __name__ == "__main__":
    # Define a non-linear state-dependent evolution matrix function M(X)
    def sample_evolution_matrix(X):
        # Simulates a feedback loop where the matrix gradually approaches a singular collapse
        return np.array([
            [0.5, X[0, 0] * 0.1],
            [0.0, 0.5]
        ])

    # Initial state matrix X_0
    X_initial = np.array([
        [2.0, 1.0],
        [1.0, 2.0]
    ])

    # Initialize engine
    engine = MatrixEvolutionEngine(X_initial, sample_evolution_matrix)
    
    # Run the discrete matrix universe
    engine.run_simulation(steps=15)
