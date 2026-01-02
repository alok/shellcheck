import Std

namespace ShellCheck.Tests.SC4xxxLists

def upstream : List Nat := []

def implemented : List Nat := [4000]

def ignored : List Nat := []

def upstreamFiltered : List Nat :=
  upstream.filter (fun code => !ignored.contains code)

def implementedFiltered : List Nat :=
  implemented.filter (fun code => !ignored.contains code)

def missing : List Nat :=
  upstreamFiltered.filter (fun code => !implementedFiltered.contains code)

def extra : List Nat :=
  implementedFiltered.filter (fun code => !upstreamFiltered.contains code)

end ShellCheck.Tests.SC4xxxLists
