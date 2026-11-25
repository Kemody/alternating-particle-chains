"""Numerical cross-checks for alternating_chains.tex. Run with Python 3 (stdlib only)."""

from cmath import exp as complex_exp
from math import exp, fsum, isclose, pi, sqrt, tanh


def signs(positions):
    return [(-1)**i for i in range(len(positions))]


def real_space_energy(positions, period, potential, copies):
    charges = signs(positions)
    return -fsum(
        charges[i] * charges[j] * potential(abs(x - y - period * n))
        for n in range(-copies, copies + 1)
        for i, x in enumerate(positions)
        for j, y in enumerate(positions)
        if n != 0 or i != j
    ) / len(positions)


def gaussian_fourier_energy(positions, period, a, modes=32):
    charges = signs(positions)
    terms = []
    for m in range(-modes, modes + 1):
        wave_number = 2 * pi * m / period
        structure = sum(c * complex_exp(1j * wave_number * x)
                        for c, x in zip(charges, positions))
        terms.append(exp(-wave_number**2 / (4*a)) * abs(structure)**2)
    return 1 - sqrt(pi / a) * fsum(terms) / (len(positions)*period)


def main():
    period = 4
    uniform = [0., 1., 2., 3.]
    displaced = [0., 1.5, 2., 2.5]
    a = 0.25
    energies = []
    print("Gaussian pair potential exp(-r^2/4), period = 4")
    print("cell                 direct sum          Fourier sum")
    for label, cell in (("uniform", uniform), ("displaced", displaced)):
        real = real_space_energy(cell, period, lambda r: exp(-a*r*r), 12)
        fourier = gaussian_fourier_energy(cell, period, a)
        assert isclose(real, fourier, rel_tol=0., abs_tol=1e-13)
        energies.append(real)
        print(f"{label:14s} {real:.15f}   {fourier:.15f}")
    print(f"Energy reduction: {energies[0] - energies[1]:.15f}")

    q = exp(-pi*pi/(16*a))
    assert 32*q**4/(1-q**4) < 4*q
    for displacement in (0.01, -0.125, 0.5, 0.9):
        cell = [0., 1.+displacement, 2., 3.-displacement]
        assert gaussian_fourier_energy(cell, period, a) < energies[0]
    print("Verified strict Fourier bound and four sample displacements.")

    # Check the exponential bound independently for a six-site cell.
    cell = [0., 0.6, 2., 2.4, 3., 4.7]
    period = 6.
    gaps = [b-a0 for a0, b in zip(cell, cell[1:] + [period])]
    for kappa in (0.2, 1., 3.):
        value = real_space_energy(cell, period, lambda r: exp(-kappa*r), 64)
        bound = 1. - fsum(tanh(kappa*d/2) for d in gaps)/len(gaps)
        minimum = 1. - tanh(kappa*period/(2*len(cell)))
        assert value >= bound - 1e-13 and bound > minimum
        print(f"kappa {kappa}: energy {value:.12f}, "
              f"gap bound {bound:.12f}, uniform {minimum:.12f}")


if __name__ == "__main__":
    main()
