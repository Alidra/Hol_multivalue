require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1076887 [A A' B B'] (g : El (fun B B')) (f' : El (fun A' A)) (g' : El (fun B' B)) (f : El (fun A A')) : Prf (⇒ (∧ ((@ISO A A') f f') ((@ISO B B') g g')) ((@ISO (fun A B) (fun A' B')) (λ h : El (fun A B), (λ a' : El A', (g (h (f' a'))))) (λ h : El (fun A' B'), (λ a : El A, (g' (h (f a)))))));
