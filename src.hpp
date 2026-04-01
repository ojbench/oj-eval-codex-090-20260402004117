// Implementation for Problem 2208: Resistive Network Calculator
#ifndef SRC_HPP
#define SRC_HPP

#include <vector>
#include <stdexcept>
#include "fraction.hpp"

class matrix {
private:
    int m, n;
    fraction **data;

    void allocate(int rows, int cols) {
        m = rows; n = cols;
        if (rows <= 0 || cols <= 0) {
            data = nullptr; m = n = 0; return;
        }
        data = new fraction*[m];
        for (int i = 0; i < m; ++i) {
            data[i] = new fraction[n];
            for (int j = 0; j < n; ++j) data[i][j] = fraction(0);
        }
    }

    void release() {
        if (!data) return;
        for (int i = 0; i < m; ++i) delete [] data[i];
        delete [] data;
        data = nullptr; m = n = 0;
    }

public:
    matrix() : m(0), n(0), data(nullptr) {}

    matrix(int m_, int n_) { data = nullptr; allocate(m_, n_); }

    matrix(const matrix &obj) {
        data = nullptr; allocate(obj.m, obj.n);
        if (data) {
            for (int i = 0; i < m; ++i)
                for (int j = 0; j < n; ++j)
                    data[i][j] = obj.data[i][j];
        }
    }

    matrix(matrix &&obj) noexcept {
        m = obj.m; n = obj.n; data = obj.data;
        obj.m = obj.n = 0; obj.data = nullptr;
    }

    ~matrix() { release(); }

    matrix &operator=(const matrix &obj) {
        if (this == &obj) return *this;
        release();
        allocate(obj.m, obj.n);
        if (data) {
            for (int i = 0; i < m; ++i)
                for (int j = 0; j < n; ++j)
                    data[i][j] = obj.data[i][j];
        }
        return *this;
    }

    fraction &operator()(int i, int j) {
        // i: 1-based row, j: 0-based column
        if (!data || i < 1 || i > m || j < 0 || j >= n) throw matrix_error();
        return data[i - 1][j];
    }

    friend matrix operator*(const matrix &lhs, const matrix &rhs) {
        if (!lhs.data || !rhs.data || lhs.n != rhs.m) throw matrix_error();
        matrix res(lhs.m, rhs.n);
        for (int i = 0; i < lhs.m; ++i) {
            for (int k = 0; k < lhs.n; ++k) {
                fraction aik = lhs.data[i][k];
                if (aik == fraction(0)) continue;
                for (int j = 0; j < rhs.n; ++j) {
                    res.data[i][j] = res.data[i][j] + (aik * rhs.data[k][j]);
                }
            }
        }
        return res;
    }

    matrix transposition() const {
        if (!data || m == 0 || n == 0) throw matrix_error();
        matrix t(n, m);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                t.data[j][i] = data[i][j];
        return t;
    }

    fraction determination() const {
        if (!data || m == 0 || n == 0 || m != n) throw matrix_error();
        // Gaussian elimination to compute determinant
        std::vector<std::vector<fraction>> a(m, std::vector<fraction>(n));
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                a[i][j] = data[i][j];

        fraction det(1);
        int sign = 1;
        for (int col = 0, row = 0; col < n && row < m; ++col) {
            int pivot = -1;
            for (int r = row; r < m; ++r) {
                if (!(a[r][col] == fraction(0))) { pivot = r; break; }
            }
            if (pivot == -1) {
                return fraction(0);
            }
            if (pivot != row) {
                std::swap(a[pivot], a[row]);
                sign = -sign;
            }
            fraction piv = a[row][col];
            det = det * piv;
            // eliminate below
            for (int r = row + 1; r < m; ++r) {
                if (a[r][col] == fraction(0)) continue;
                fraction factor = a[r][col] / piv;
                for (int c = col; c < n; ++c) {
                    a[r][c] = a[r][c] - factor * a[row][c];
                }
            }
            ++row;
        }
        if (sign == -1) det = fraction(0) - det; // multiply by -1
        return det;
    }

    // Helpers
    int rows() const { return m; }
    int cols() const { return n; }
    fraction get(int i, int j) const { return data[i][j]; }
};

class resistive_network {
private:
    int interface_size, connection_size;
    matrix adjacency;   // m x n incidence matrix
    matrix conduction;  // m x m diagonal of conductances

    static bool is_zero(const fraction &x) { return x == fraction(0); }

    // Build Laplacian L = A^T * C * A
    matrix build_laplacian() const {
        matrix At = adjacency.transposition();
        matrix CA = conduction * adjacency;
        matrix L = At * CA;
        return L; // n x n
    }

    // Solve linear system M x = b via Gaussian elimination (exact fractions).
    // M is square (k x k), b is size k (as vector<matrix> row fractions)
    static std::vector<fraction> solve(const matrix &M, const std::vector<fraction> &b) {
        int k = M.rows();
        if (M.cols() != k || (int)b.size() != k) throw resistive_network_error();

        std::vector<std::vector<fraction>> a(k, std::vector<fraction>(k + 1));
        for (int i = 0; i < k; ++i) {
            for (int j = 0; j < k; ++j) a[i][j] = M.get(i, j);
            a[i][k] = b[i];
        }

        int row = 0;
        for (int col = 0; col < k && row < k; ++col) {
            int pivot = -1;
            for (int r = row; r < k; ++r) {
                if (!(a[r][col] == fraction(0))) { pivot = r; break; }
            }
            if (pivot == -1) continue; // singular but assumed solvable
            if (pivot != row) std::swap(a[pivot], a[row]);
            fraction piv = a[row][col];
            // normalize row
            for (int c = col; c <= k; ++c) a[row][c] = a[row][c] / piv;
            // eliminate other rows
            for (int r = 0; r < k; ++r) {
                if (r == row) continue;
                if (a[r][col] == fraction(0)) continue;
                fraction factor = a[r][col];
                for (int c = col; c <= k; ++c) {
                    a[r][c] = a[r][c] - factor * a[row][c];
                }
            }
            ++row;
        }
        std::vector<fraction> x(k, fraction(0));
        for (int i = 0; i < k; ++i) x[i] = a[i][k];
        return x;
    }

public:
    resistive_network(int interface_size_, int connection_size_, int from[], int to[], fraction resistance[]) :
        interface_size(interface_size_), connection_size(connection_size_),
        adjacency(connection_size_, interface_size_), conduction(connection_size_, connection_size_) {
        // Build incidence matrix A (m x n)
        for (int e = 0; e < connection_size; ++e) {
            int u = from[e];
            int v = to[e];
            // orientation: from -> to
            adjacency(e + 1, u - 1) = fraction(1);
            adjacency(e + 1, v - 1) = fraction(-1);
        }
        // Build conductance diagonal matrix C (m x m)
        for (int e = 0; e < connection_size; ++e) {
            fraction g = fraction(1) / resistance[e];
            conduction(e + 1, e) = g;
        }
    }

    ~resistive_network() = default;

    fraction get_equivalent_resistance(int interface_id1, int interface_id2) {
        // Equivalent resistance between a and b: inject 1A from a to b, set b as ground
        int a = interface_id1;
        int b = interface_id2;
        matrix L = build_laplacian(); // n x n

        // Build reduced system by removing row/col b
        int k = interface_size - 1;
        matrix Lr(k, k);
        int ri = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == b) continue;
            int rj = 0;
            for (int j = 0; j < interface_size; ++j) {
                if (j + 1 == b) continue;
                Lr(ri + 1, rj) = L.get(i - 1, j);
                ++rj;
            }
            ++ri;
        }
        std::vector<fraction> Ir(k, fraction(0));
        // current vector: +1 at a, -1 at b; after removing b, Ir index for a is adjusted
        int idx = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == b) continue;
            Ir[idx] = (i == a) ? fraction(1) : fraction(0);
            ++idx;
        }
        std::vector<fraction> Ur = solve(Lr, Ir);
        // Voltage at a relative to ground b
        fraction Va = fraction(0);
        idx = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == b) continue;
            if (i == a) { Va = Ur[idx]; break; }
            ++idx;
        }
        return Va;
    }

    fraction get_voltage(int id, fraction current[]) {
        // Ground node is interface_size; solve L_red U_red = I_red
        matrix L = build_laplacian();
        int ground = interface_size;
        int k = interface_size - 1;
        matrix Lr(k, k);
        int ri = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == ground) continue;
            int rj = 0;
            for (int j = 0; j < interface_size; ++j) {
                if (j + 1 == ground) continue;
                Lr(ri + 1, rj) = L.get(i - 1, j);
                ++rj;
            }
            ++ri;
        }
        std::vector<fraction> Ir(k, fraction(0));
        int idx = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == ground) continue;
            Ir[idx] = current[i - 1];
            ++idx;
        }
        std::vector<fraction> Ur = solve(Lr, Ir);
        // Return voltage at id (if id is ground, it's 0 by definition; but they guarantee id < ground)
        fraction V = fraction(0);
        idx = 0;
        for (int i = 1; i <= interface_size; ++i) {
            if (i == ground) continue;
            if (i == id) { V = Ur[idx]; break; }
            ++idx;
        }
        return V;
    }

    fraction get_power(fraction voltage[]) {
        // Power = sum over edges g * (u_from - u_to)^2
        fraction total(0);
        for (int e = 0; e < connection_size; ++e) {
            // find endpoints
            int u = -1, v = -1;
            // Read from adjacency row e: +1 at from, -1 at to
            for (int j = 0; j < interface_size; ++j) {
                fraction val = adjacency.get(e, j);
                if (val == fraction(1)) u = j + 1;
                else if (val == fraction(-1)) v = j + 1;
            }
            if (u == -1 || v == -1) throw resistive_network_error();
            fraction du = voltage[u - 1] - voltage[v - 1];
            fraction g = conduction.get(e, e);
            total = total + g * du * du;
        }
        return total;
    }
};

#endif // SRC_HPP
