require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3354637 [A] : Prf (= (∀ (λ x : El A, (= ((@IN A) x ((@INTERS A) (@EMPTY (fun A bool)))) ((@IN A) x (@UNIV A))))) (= ((@INTERS A) (@EMPTY (fun A bool))) (@UNIV A)));
