import itertools
import random

def is_valid_SYT(candidate):
  """
  Check if the given candidate tableau is a valid standard Young tableau.

  Parameters:
  - candidate (Tuple[Tuple[int]]): The tableau to be checked.

  Returns:
  - bool: True if the matrix is valid, False otherwise.

  The function checks if the given matrix is a valid SYT matrix by verifying that:
  1. The elements in each column are in strictly increasing order.
  2. The elements in each row are in strictly increasing order.

  Example:
  >>> is_valid_SYT(((1, 2, 3), (4, 5, 6), (7, 8, 9)))
  True
  >>> is_valid_SYT(((1, 2, 3), (5, 4), (6))
  False
  """
  for x in range(len(candidate)):
    for y in range(len(candidate[x])):
      if (candidate[x][y] >= candidate[x+1][y]) and x < (len(candidate) - 1) and y < (len(candidate[y + 1])):
        return False 
      elif (candidate[x][y] >= [x][y+1] and y < len(candidate[x]) - 1):
        return False 
  return True

def reshape_perm(perm, shape):
  """
  Reshapes a permutation into a tableau based on the given shape.

  Parameters:
  - perm (Tuple[int]): The permutation to be reshaped.
  - shape (Tuple[int]): The shape of the resulting tableau as a weakly decreasing tuple of integers.

  Returns:
  - Tuple[Tuple[int]]: A tuple of tuples representing the reshaped permutation as a tableau.

  Example:
  >>> reshape_perm((1, 2, 3, 4, 5, 6), (3, 2, 1))
  ((1, 2, 3), (4, 5), (6,))
  """
  # return tuple()
  listish = []
  ind = 0
  for x in shape: 
    togo = ind + x
    listish.append(tuple(perm[ind:togo]))
    ind = togo
  return tuple(listish) 

def SYTs(shape):
  """
  Generates SYTs (Standard Young Tableaux) of on the given shape.

  Parameters:
  - shape (Tuple[int]): The shape of the resulting SYTs as a tuple of integers.

  Returns:
  - List[Tuple[Tuple[int]]]: A list of valid SYTs generated based on the given shape.

  Example:
  >>> SYTs((2, 1))
  [((1, 2), (3,)), ((1, 3), (2,))]
  """

  n = sum(shape)
  results = []
  allNum = itertools.permutations(range(1, n + 1), n)
  for x in allNum: 
    if (is_valid_SYT(reshape_perm(x, shape))):
      results.append(reshape_perm(x, shape))
  return results

def random_SYT(shape):
  """
  Generates a random Standard Young Tableau (SYT) of the given shape.

  Parameters:
  - shape (Tuple[int]): The shape of the resulting SYT as a tuple of integers.

  Returns:
  - Tuple[Tuple[int]]: A random valid SYT generated based on the given shape.

  This function generates a random permutation of numbers from 1 to n+1, where n is the sum of the elements in the `shape` tuple. It then reshapes the permutation into a tableau using the `reshape_perm` function. If the resulting tableau is not valid, it shuffles the permutation and tries again. The function continues this process until a valid SYT is found, and then returns the reshaped permutation as a tableau.

  Example:
  >>> random_SYT((2, 1))
  ((1, 2), (3,))
  """
  n = sum(shape)
  x = list(range(1, n +1))
  random.shuffle(x)
  notval = False
  while (not notval):
    if (not is_valid_SYT(reshape_perm(x, shape))):
      random.shuffle(x)
    else: 
      notval = True 
  return reshape_perm(x, shape)

def random_SYT_2(shape):
  """
  Generates a random Standard Young Tableau (SYT) of the given shape.

  Parameters:
  - shape (Tuple[int]): The shape of the resulting SYT as a tuple of integers.

  Returns:
  - Tuple[Tuple[int]]: A random valid SYT generated based on the given shape.

  The function generates a random SYT by starting off with the all zeroes tableau and greedily filling in the numbers from 1 to n. The greedy generation is repeated until a valid SYT is produced.

  Example:
  >>> random_SYT_2((2, 1))
  ((1, 2), (3,))
  """
  n = sum(shape)
  numbers = list(range(1, n + 1))      
  while True:
        random.shuffle(numbers) 
        tableau = [] 
        index = 0
        valid = True
        for row_length in shape:
            row = numbers[index:index + row_length]
            tableau.append(row)
            index += row_length
        for i in range(len(tableau)):
            for j in range(len(tableau[i])):
                if j > 0 and tableau[i][j] <= tableau[i][j - 1]:
                    valid = False
                if i > 0 and tableau[i][j] <= tableau[i - 1][j]:
                    valid = False
                if not valid:
                    break
            if not valid:
                break
        
        if valid:
            break 
  return tuple(tuple(row) for row in tableau)
