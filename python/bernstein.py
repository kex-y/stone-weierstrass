import numpy as np
from setup import user_input

def bernstein_poly(f, n):
    from math import factorial
    choose = lambda n, k: factorial(n) // (factorial(k) * factorial(n - k))
    return lambda x: sum([f(k / n) * choose(n, k) * x**k * (1 - x)**(n - k) for k in range(n + 1)])

def approx_plot(is_seq = False): 
    import matplotlib.pyplot as plt

    f, n = user_input()
    x_vals = np.linspace(-1, 1, 100)

    if is_seq == False:
        approx_y_vals = np.vectorize(bernstein_poly(f, n))(x_vals)
        label_str = "{}-th Bernstein Approx." .format(n)
        plt.plot(x_vals, approx_y_vals, label = label_str)
    else:
        for i in range(1, n + 1):
            approx_y_vals = np.vectorize(bernstein_poly(f, i))(x_vals)
            label_str = "{}-th Bernstein Approx." .format(i)
            plt.plot(x_vals, approx_y_vals, label = label_str)

    plt.plot(x_vals, f(x_vals), label = "$x^2$")
    plt.legend(loc = "best")
    plt.show()

approx_plot(is_seq = True)