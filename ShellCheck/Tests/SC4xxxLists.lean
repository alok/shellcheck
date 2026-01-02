import Std

namespace ShellCheck.Tests.SC4xxxLists

def upstream : List Nat := []

def implemented : List Nat := [4000]

def missing : List Nat :=
  upstream.filter (fun code => !implemented.contains code)

def extra : List Nat :=
  implemented.filter (fun code => !upstream.contains code)

end ShellCheck.Tests.SC4xxxLists
