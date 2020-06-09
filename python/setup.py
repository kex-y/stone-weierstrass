import numpy as np

def user_input():
    func_str = input("Function to be approximated (as a lambda function): ")
    n_str = input("To the degree: ") 
    return (eval(func_str), eval(n_str))