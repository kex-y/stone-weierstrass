import numpy as np

def user_input():
    func_str = input("Function to be approximated (as a lambda function): ")
    n_str = input("To the degree: ") 
    return (eval(func_str), eval(n_str))

def bernstein_poly(f, n):
    from math import factorial
    choose = lambda n, k: factorial(n) // (factorial(k) * factorial(n - k))
    return lambda x: sum([f(k / n) * choose(n, k) * x**k * (1 - x)**(n - k) for k in range(n + 1)])

def approx_plot(is_seq = False): 
    import matplotlib.pyplot as plt

    f, n = user_input()
    x_vals = np.linspace(-5, 5, 100)

    if is_seq == False:
        approx_y_vals = np.vectorize(bernstein_poly(f, n))(x_vals)
        plt.plot(x_vals, approx_y_vals)
    else:
        for i in range(1, n + 1):
            approx_y_vals = np.vectorize(bernstein_poly(f, i))(x_vals)
            plt.plot(x_vals, approx_y_vals)
    plt.plot(x_vals, f(x_vals))
    plt.show()

approx_plot(is_seq = True)