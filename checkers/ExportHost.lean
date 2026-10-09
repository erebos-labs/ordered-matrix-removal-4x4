import OrderedMatrixRemoval4.Host
open OrderedMatrixRemoval4.Host

def formatPosition : Position → String
  | .anchor l k g a => s!"A,{l},{k},{g},{a}"
  | .variable i s p a => s!"T,{i},{if s then 1 else 0},{p},{a}"
  | .dummy a => s!"D,{a}"

#eval do
  for h in [1, 2] do
    let lines := List.ofFn fun r : Fin (size h) =>
      String.ofList (List.ofFn fun c : Fin (size h) => if matrix h r c then '1' else '0')
    IO.FS.writeFile s!"evidence/lean-host-h{h}.txt" (String.intercalate "\n" lines ++ "\n")
    for col in [false, true] do
      let tags := (axis col h).map formatPosition
      IO.FS.writeFile s!"evidence/lean-axis-{if col then "c" else "r"}-h{h}.txt"
        (String.intercalate "\n" tags ++ "\n")
