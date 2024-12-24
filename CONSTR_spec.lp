require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1059607 [A] : Prf (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (recspace A)), (= ((@CONSTR A) c i r) ((@_mk_rec A) ((@ZCONSTR A) c i (λ n : El num, ((@_dest_rec A) (r n))))))))))));
