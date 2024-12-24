require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4628778 : Prf (∀ (λ s : El (fun num bool), (= ((@INFINITE num) s) (∀ (λ N : El num, (∃ (λ n : El num, (∧ (<= N n) ((@IN num) n s)))))))));
