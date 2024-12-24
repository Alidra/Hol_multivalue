require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248646 (d : El num) (d' : El num) (d'' : El num) : Prf (= (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d''')))))) (<= d (+ d' d'')));
