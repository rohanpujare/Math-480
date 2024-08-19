import itertools

def parenthesizations(n):
  """
  Returns a set of all possible parenthesizations of length n.

  Parameters:
    n (int): The length of the parenthesizations.

  Returns:
    A set of strings, where each inner string represents a valid parenthesization of length n.
  
  Example:
  >>> parenthesizations(3)
  {'((()))', '(()())', '(())()', '()(())', '()()()'}
  """
  if n == 0:
    return {""}
  else:
    return genPar('', n, n)
    def genPar(p, l, r, par = []):
      if l: genPar(p + '(', l - 1, r)
      if r > l: genPar(p + ')', l, r - 1)
      if not r: par += p,
      return par
    #pass

def product_orders(n):
  """
  Returns a set of all possible ways to multiply of n elements.

  Parameters:
    n (int): The number of elements multiplied.

  Returns:
    A set of strings where each string represents a way to multiply n elements.
  
  Example:
  >>> product_orders(4)
  {'((?*?)*?)*?', '(?*(?*?))*?', '(?*?)*(?*?)', '?*((?*?)*?)', '?*(?*(?*?))'}
  """
  if n == 0:
    return {""}
  elif n == 1:
    return {"?"}
  elif n == 2:
    return {"?*?"}
  else:
    # TODO
    res = set()
    for x in range (1, n):
      beg = product_orders(x)
      end = product_orders(n - x)
      for b in beg: 
        for e in end: 
          res.add("({b}*{e})")

    return res
    #pass

def permutations_avoiding_231(n):
  """
  Returns a set of permutations of length n avoiding the pattern 2-3-1.
  
  Parameters:
    n (int): The length of the permutation.
  
  Returns:
    A set of permutations of length n that do not contain the pattern 2-3-1.
  
  Example:
  >>> permutations_avoiding_231(4)
  {(1, 2, 3, 4), (1, 2, 4, 3), (1, 3, 2, 4), (1, 4, 2, 3), (1, 4, 3, 2), (2, 1, 3, 4), (2, 1, 4, 3), (3, 1, 2, 4), (3, 2, 1, 4), (4, 1, 2, 3), (4, 1, 3, 2), (4, 2, 1, 3), (4, 3, 1, 2), (4, 3, 2, 1)}
  """
  if n < 3:
    return set(itertools.permutations(range(1, n+1)))
  else:
    # TODO
    res = set()
    res = set(itertools.permutations(range(1, n + 1)))
    for possible in res: 
      a = false 
      subcheck = []
      for elem in possible: 
        if elem == 1 or elem == 2 or elem == 3:
          subcheck.__add__(elem)
      if subcheck.__eq__(2, 3, 1):
        res.remove(possible)
    return res
    # pass

def triangulations(n):
  """
  Returns a set of all possible triangulations of an n-sided polygon. A triangulation
  is represented as a tuple of internal edges. Vertices are labeled 0 through n-1 clockwise.

  Parameters:
    n (int): The number of sides of the polygon.

  Returns:
    A set of tuple of pairs, where each pair represents an internal edge in the triangulation.
  
  Example:
  >>> triangulations(3)
  {((0, 3), (1, 3)), ((1, 4), (2, 4)), ((1, 3), (1, 4)), ((0, 2), (2, 4)), ((0, 2), (0, 3))}
  """
  if n < 3:
    return set()
  elif n == 3:
    return {tuple()}
  else:
    #pass
    # TODO
    res = set()

    # induction = recursion 

    for x in range (1, n): 
      for t in triangulations(x):
        for b in triangulations(n - x):
          toAdd = [(0,i)] + list(t) + [(i + x),(j + x) for (i, j) in t] 
          res.add(tuple(toAdd))
    return res
