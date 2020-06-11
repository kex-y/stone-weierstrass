import numpy as np; from numpy.polynomial.polynomial import Polynomial
from setup import user_input

# We will use np.vander() to generate the Vandermonde matrix
def lagrange_interpolation(x_vals, y_vals):
    vander_mat = np.vander(x_vals)
    coe = np.linalg.inv(vander_mat).dot(np.transpose(y_vals))
    return coe[::-1]

def interpolation_plot():
    import matplotlib.pyplot as plt

    f, n, f_str = user_input()
    x_vals = np.linspace(-1, 1, n + 1)
    y_vals = f(x_vals)
    p = Polynomial(lagrange_interpolation(x_vals, y_vals))

    x_vals = np.linspace(-1, 1, 100)
    plt.plot(x_vals, p(x_vals), label = "Interpolation")
    plt.plot(x_vals, f(x_vals), label = f_str)
    plt.legend(loc = "best"); plt.show()

interpolation_plot()