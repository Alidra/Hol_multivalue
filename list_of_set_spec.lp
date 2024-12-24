require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4786583 [_110256] : Prf (∀ (λ s : El (fun _110256 bool), (= ((@list_of_set _110256) s) ((@ε (list _110256)) (λ l : El (list _110256), (∧ (= ((@set_of_list _110256) l) s) (= ((@LENGTH _110256) l) ((@CARD _110256) s))))))));
