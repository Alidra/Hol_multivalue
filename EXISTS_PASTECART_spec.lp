require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7664353 [_140476 _140477 _140478] (P : El (fun (cart _140476 (finite_sum _140477 _140478)) bool)) : Prf (= (∃ (λ p : El (cart _140476 (finite_sum _140477 _140478)), (P p))) (∃ (λ x : El (cart _140476 _140477), (∃ (λ y : El (cart _140476 _140478), (P ((@pastecart _140476 _140477 _140478) x y)))))));
