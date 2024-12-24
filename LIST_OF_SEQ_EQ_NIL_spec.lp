require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1237614 [A] : Prf (∀ (λ s : El (fun num A), (∀ (λ n : El num, (= (= ((@list_of_seq A) s n) (@NIL A)) (= n (NUMERAL _0)))))));
