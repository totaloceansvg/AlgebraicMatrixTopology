import numpy as np

class MatrixBurgersShockEngine:
    def __init__(self, spatial_nodes=32, dt=0.005):
        self.N = spatial_nodes
        self.dt = dt
        x = np.linspace(0, 2 * np.pi, self.N)
        u_init = 1.0 - 0.8 * np.tanh(5.0 * (x - np.pi))
        self.X = np.outer(u_init, u_init)
        self.projector_count = 0

    def evolution_operator_M(self, X):
        norm_val = np.linalg.norm(X)
        return 0.5 * np.eye(self.N) + 0.05 * (X / (norm_val + 1e-8))

    def generate_idempotent_projector(self, matrix, tol=1e-4):
        U, s, Vt = np.linalg.svd(matrix)
        active_dims = np.sum(s > tol)
        if active_dims < 2: active_dims = 2
        U_r = U[:, :active_dims]
        return U_r @ U_r.T

    def step(self):
        M = self.evolution_operator_M(self.X)
        X_next = M @ self.X + self.dt * (M @ M - self.X)
        
        max_dim = X_next.shape[0]
        current_rank = np.linalg.matrix_rank(X_next, tol=1e-5)
        is_singular_threat = (current_rank < max_dim - 2) or np.any(np.isnan(X_next))
        
        if is_singular_threat:
            P = self.generate_idempotent_projector(X_next)
            assert np.allclose(P @ P, P, atol=1e-6) # Machine verification of P^2 = P
            X_next = P @ X_next @ P
            self.projector_count += 1
            
        self.X = X_next
        return self.X
