'''
==============
3D scatterplot
==============

Demonstration of a basic scatterplot in 3D.
'''

from mpl_toolkits.mplot3d import Axes3D
import matplotlib.pyplot as plt
import numpy as np
#import pandas as pd
import math

def sctr(arr,zlbl='',ttl='',sz=20,c=None,m='^',log=True,dpthshd=True,trnspr=0.5):

    fig = plt.figure()
    ax = fig.add_subplot(111, projection='3d')

    X = np.arange(2,10,1)
    Y = np.arange(2,7,1)
    xs, ys = np.meshgrid(X, Y)
    if log:
        zs = np.log10( arr )
    else:
        zs = ( arr )
    ax.scatter(xs, ys, zs, s=sz,c=c, marker=m,depthshade=dpthshd,alpha=trnspr)


    ax.set_xlabel('No. of Attributes')
    ax.set_ylabel('Log10 of No. of Tuples')
    ax.set_zlabel(zlbl)
    ax.set_title(ttl)

    plt.show()

#Array of actual Time Taken
arr_t = np.array([[0.007,0.012,0.036,0.109,0.298,0.87,1.938,4.519],
    [0.015,0.026,0.093,0.276,0.63,1.732,4.341,9.351],
        [0.053,0.176,0.593,1.658,4.23,11.13,25.848,68.965],
        [0.365,1.794,5.783,15.87,42.829,103.294,232.273,582.368],
        [4.001,20.416,60.685,161.787,422.698,1021.295,2437.97,6004.19]])

#Theoritical serial complexity
arr_s = np.array([[       200,       1800,       8400,      30000,      93000,
            264600,     711200,    1836000],
        [       2000,       18000,       84000,      300000,      930000,
            2646000,     7112000,    18360000],
       [      20000,      180000,      840000,     3000000,     9300000,
           26460000,    71120000,   183600000],
       [     200000,     1800000,     8400000,    30000000,    93000000,
          264600000,   711200000,  1836000000],
       [    2000000,    18000000,    84000000,   300000000,   930000000,
         2646000000,  7112000000, 18360000000]])

#Number of Cores possible
arr_c = np.array([[     200,      600,     1200,     3000,     6000,    14000,
           28000,    63000],
        [     2000,      6000,     12000,     30000,     60000,    140000,
           280000,    630000],
       [    20000,     60000,    120000,    300000,    600000,   1400000,
          2800000,   6300000],
       [   200000,    600000,   1200000,   3000000,   6000000,  14000000,
         28000000,  63000000],
       [  2000000,   6000000,  12000000,  30000000,  60000000, 140000000,
        280000000, 630000000]])

#Actual Parallel steps
arr_ps = np.array([[  1.,   3.,   6.,  10.,  15.,  21.,  28.,  36.],
        [  1.,   3.,   6.,  10.,  15.,  21.,  28.,  36.],
       [  1.,   3.,   6.,  10.,  15.,  21.,  28.,  36.],
       [  1.,   3.,   6.,  10.,  15.,  21.,  28.,  36.],
       [  1.,   3.,   6.,  10.,  15.,  21.,  28.,  36.]])


    
'''
XR = [2,3,4,5,6,7,8,9]
YR = [4.001,20.416,60.685,161.787,422.698,1021.295,2437.97,6004.19]

_ = plt.plot(XR,np.log(YR))
plt.show()

XC = [0,1,2,3,4,5,6]
YC = [3.963,4.1,4.519,9.351,68.965,582.368,6004.19]

_ = plt.plot(XC,np.log(YC))
plt.show()

def f(T,N):
    'Steps needed'
    return T*N*(N-1)*(2**(N-1)-1)

def comb(N,R):
    return fct(N)//(fct(R)*fct(N-R))

def g(T,N):
    'MAX Cores Possible'
    return T*N*comb((N-1),round((N-1)/2))

def h(T,N):
    'Parallel Steps needed'
    return N*(N-1)/2




'''
