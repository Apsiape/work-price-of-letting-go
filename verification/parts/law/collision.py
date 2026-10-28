"""Exact K-step collision action used by check_speed_order.py.

Binary relative entropy d(p||q) in nats, Bhattacharyya angle theta(q) = arcsin sqrt q, and the exact K-step action
    A_K(a, b) = min over q_1..q_{K-1} of sum_{j=1}^K d(q_{j-1} || q_j),  q_0 = a, q_K = b,
solved by damped Newton on the jointly convex tridiagonal program.
"""
import numpy as np

def d(p, q):
    """Binary relative entropy in nats, written with log1p so that nearby arguments do not cancel."""
    p = np.asarray(p, float); q = np.asarray(q, float)
    with np.errstate(divide='ignore', invalid='ignore'):
        t1 = np.where(p > 0, p * np.log1p((p - q) / q), 0.0)
        t2 = np.where(p < 1, (1 - p) * np.log1p((q - p) / (1 - q)), 0.0)
    return t1 + t2

def h(p):
    p = np.asarray(p, float)
    with np.errstate(divide='ignore', invalid='ignore'):
        a = np.where(p > 0, -p * np.log(p), 0.0)
        b = np.where(p < 1, -(1 - p) * np.log(1 - p), 0.0)
    return a + b

def theta(q):
    return np.arcsin(np.sqrt(q))

def length(a, b):
    """Fisher-Rao (thermodynamic) length between Bernoulli(a) and Bernoulli(b)."""
    return 2.0 * abs(theta(a) - theta(b))

def action_value(q):
    q = np.asarray(q, float)
    return float(np.sum(d(q[:-1], q[1:])))

def geodesic_path(a, b, K):
    th = np.linspace(theta(a), theta(b), K + 1)
    return np.sin(th) ** 2

def A_K(a, b, K, tol=1e-15, maxit=500, q0=None):
    """Exact minimum of sum_j d(q_{j-1}||q_j) over K steps from a to b.
    Returns (value, path)."""
    if K == 1:
        q = np.array([a, b], float)
        return action_value(q), q
    q = geodesic_path(a, b, K) if q0 is None else np.array(q0, float)
    q[0], q[-1] = a, b
    f = action_value(q)
    for it in range(maxit):
        x = q[1:-1]; xm = q[:-2]; xp = q[2:]
        g = (x - xm) / (x * (1 - x)) + np.log(x / xp) - np.log((1 - x) / (1 - xp))
        diag = xm / x**2 + (1 - xm) / (1 - x)**2 + 1 / x + 1 / (1 - x)
        off = -1.0 / (xp[:-1] * (1 - xp[:-1]))   # d^2/dq_j dq_{j+1}
        n = len(x)
        # solve tridiagonal H s = -g (Thomas algorithm)
        a_ = np.zeros(n); b_ = diag.copy(); c_ = np.zeros(n); r = -g.copy()
        a_[1:] = off; c_[:-1] = off
        for i in range(1, n):
            m = a_[i] / b_[i - 1]
            b_[i] -= m * c_[i - 1]; r[i] -= m * r[i - 1]
        s = np.zeros(n); s[-1] = r[-1] / b_[-1]
        for i in range(n - 2, -1, -1):
            s[i] = (r[i] - c_[i] * s[i + 1]) / b_[i]
        dec = -float(g @ s)
        # keep inside (0,1): cap step multiplicatively
        t = 1.0
        while True:
            xn = x + t * s
            if np.all(xn > 0) and np.all(xn < 1):
                qn = q.copy(); qn[1:-1] = xn
                fn = action_value(qn)
                if fn <= f - 1e-4 * t * dec or t < 1e-12:
                    break
            t *= 0.5
        q, f_old, f = qn, f, fn
        if dec < tol or abs(f_old - f) < 1e-17 * max(1, abs(f)):
            if dec < 1e-13:
                break
    return f, q

def grad_norm(q):
    x = q[1:-1]; xm = q[:-2]; xp = q[2:]
    g = (x - xm) / (x * (1 - x)) + np.log(x / xp) - np.log((1 - x) / (1 - xp))
    return float(np.max(np.abs(g * x * (1 - x)))) if len(x) else 0.0
