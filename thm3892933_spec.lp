require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3892933 [_100607] (n : El num) (P : El (fun (fun _100607 bool) bool)) : Prf (∧ (= (∃ (λ s : El (fun _100607 bool), (∧ ((@HAS_SIZE _100607) s (NUMERAL _0)) (P s)))) (P (@EMPTY _100607))) (= (∃ (λ s : El (fun _100607 bool), (∧ ((@HAS_SIZE _100607) s (SUC n)) (P s)))) (∃ (λ a : El _100607, (∃ (λ s : El (fun _100607 bool), (∧ ((@HAS_SIZE _100607) s n) (∧ (¬ ((@IN _100607) a s)) (P ((@INSERT _100607) a s))))))))));
