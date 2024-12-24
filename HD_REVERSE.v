Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HD_REVERSE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LAST_REVERSE_spec.
Require Import REVERSE_EQ_EMPTY_spec.
Require Import REVERSE_REVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1203979 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1203980 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem1203979 (term1 A)). Qed.
Lemma lem1203981 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem1203980 A)). Qed.
Lemma lem1203982 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem1203983 {A : Type'} : term4 A.
Proof. exact (@lem1203967 A). Qed.
Lemma lem1203985 {A : Type'} : term5 A.
Proof. exact (@lem1203967 (list A)). Qed.
Lemma lem1203990 {A : Type'} : term6 A.
Proof. exact (@lem1112270 A). Qed.
Lemma lem1203991 {A : Type'} : term7 A.
Proof. exact (@lem1112270 (list A)). Qed.
Lemma lem1203994 {A : Type'} : term8 A.
Proof. exact (@lem1113347 A). Qed.
Lemma lem1203995 {A : Type'} : term9 A.
Proof. exact (@lem1113347 (list A)). Qed.
Lemma lem1204002 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem1204003 {A : Type'} : term11 A.
Proof. exact (fun h0 : term10 A => @lem1204002 A h0). Qed.
Lemma lem1204004 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem1204005 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem1204006 {A : Type'} (h1 : term10 A) (h2 : term11 A) : term10 A.
Proof. exact (@lem1204004 A h2 (@lem1204005 A h1)). Qed.
Lemma lem1204007 {A : Type'} (h1 : term10 A) : term12 A.
Proof. exact (fun h0 : term11 A => @lem1204006 A h1 h0). Qed.
Lemma lem1204008 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem1204009 {A : Type'} (h1 : term10 A) (h2 : term11 A) : term10 A.
Proof. exact (@lem1204007 A h1 (@lem1204008 A h2)). Qed.
Lemma lem1204010 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (fun h0 : term10 A => @lem1204009 A h0 h1). Qed.
Lemma lem1204011 {A : Type'} : term13 A.
Proof. exact (fun h0 : term11 A => @lem1204010 A h0). Qed.
Lemma lem1204014 {A : Type'} : term11 A.
Proof. exact (@lem1204011 A (@lem1204003 A)). Qed.
Lemma lem1204015 {A : Type'} : term11 A.
Proof. exact (@lem1204014 A). Qed.
Lemma lem1204057 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1204058 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (@lem1204057 (term5 A)). Qed.
Lemma lem1204065 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem1204066 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem1204065 A) (@lem1204058 A)). Qed.
Lemma lem1204069 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem1204070 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem1204069 A) (@lem1204066 A)). Qed.
Lemma lem1204073 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem1204074 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1204073 A) (@lem1204070 A)). Qed.
Lemma lem1204077 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem1204078 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem1204077 A) (@lem1204074 A)). Qed.
Lemma lem1204081 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem1204082 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (MK_COMB (@lem1204081 A) (@lem1204078 A)). Qed.
Lemma lem1204085 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (eq_refl (term31 A)). Qed.
Lemma lem1204092 {A : Type'} : (term10 A) = (term32 A).
Proof. exact (MK_COMB (@lem1204085 A) (@lem1204082 A)). Qed.
Lemma lem1204099 {A : Type'} (l : type1628 A) : (term33 A l) = (term33 A l).
Proof. exact (eq_refl (term33 A l)). Qed.
Lemma lem1204100 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun l : type1628 A => @lem1204099 A l)). Qed.
Lemma lem1204101 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1204102 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem1204101 A) (@lem1204100 A)). Qed.
Lemma lem1204103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1204104 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem1204103) (@lem1204102 A)). Qed.
Lemma lem1204111 {A : Type'} (l : list A) : (term35 A l) = (term35 A l).
Proof. exact (eq_refl (term35 A l)). Qed.
Lemma lem1204112 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun l : list A => @lem1204111 A l)). Qed.
Lemma lem1204113 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204114 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem1204113 A) (@lem1204112 A)). Qed.
Lemma lem1204115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204116 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem1204115) (@lem1204114 A)). Qed.
Lemma lem1204117 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem1204116 A) (@lem1204104 A)). Qed.
Lemma lem1204118 {A : Type'} (l : type1628 A) : ((term37 A l) = l) = ((term37 A l) = l).
Proof. exact (eq_refl ((term37 A l) = l)). Qed.
Lemma lem1204119 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun l : type1628 A => @lem1204118 A l)). Qed.
Lemma lem1204120 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1204121 {A : Type'} : (term7 A) = (term7 A).
Proof. exact (MK_COMB (@lem1204120 A) (@lem1204119 A)). Qed.
Lemma lem1204122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204123 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem1204122) (@lem1204121 A)). Qed.
Lemma lem1204124 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem1204123 A) (@lem1204117 A)). Qed.
Lemma lem1204125 {A : Type'} (l : list A) : ((term39 A l) = l) = ((term39 A l) = l).
Proof. exact (eq_refl ((term39 A l) = l)). Qed.
Lemma lem1204126 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun l : list A => @lem1204125 A l)). Qed.
Lemma lem1204127 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204128 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1204127 A) (@lem1204126 A)). Qed.
Lemma lem1204129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204130 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem1204129) (@lem1204128 A)). Qed.
Lemma lem1204131 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem1204130 A) (@lem1204124 A)). Qed.
Lemma lem1204136 {A : Type'} (l : type1628 A) : (((@List.rev (list A) l) = (@nil (list A))) = (l = (@nil (list A)))) = (((@List.rev (list A) l) = (@nil (list A))) = (l = (@nil (list A)))).
Proof. exact (eq_refl (((@List.rev (list A) l) = (@nil (list A))) = (l = (@nil (list A))))). Qed.
Lemma lem1204137 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (fun_ext (fun l : type1628 A => @lem1204136 A l)). Qed.
Lemma lem1204138 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1204139 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (MK_COMB (@lem1204138 A) (@lem1204137 A)). Qed.
Lemma lem1204140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204141 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem1204140) (@lem1204139 A)). Qed.
Lemma lem1204142 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem1204141 A) (@lem1204131 A)). Qed.
Lemma lem1204147 {A : Type'} (l : list A) : (((@List.rev A l) = (@nil A)) = (l = (@nil A))) = (((@List.rev A l) = (@nil A)) = (l = (@nil A))).
Proof. exact (eq_refl (((@List.rev A l) = (@nil A)) = (l = (@nil A)))). Qed.
Lemma lem1204148 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (fun_ext (fun l : list A => @lem1204147 A l)). Qed.
Lemma lem1204149 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204150 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem1204149 A) (@lem1204148 A)). Qed.
Lemma lem1204151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204152 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem1204151) (@lem1204150 A)). Qed.
Lemma lem1204153 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem1204152 A) (@lem1204142 A)). Qed.
Lemma lem1204160 {A : Type'} (l : list A) : (term43 A l) = (term43 A l).
Proof. exact (eq_refl (term43 A l)). Qed.
Lemma lem1204161 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (fun_ext (fun l : list A => @lem1204160 A l)). Qed.
Lemma lem1204162 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204163 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem1204162 A) (@lem1204161 A)). Qed.
Lemma lem1204164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1204165 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem1204164) (@lem1204163 A)). Qed.
Lemma lem1204166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1204167 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem1204166) (@lem1204165 A)). Qed.
Lemma lem1204168 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem1204167 A) (@lem1204153 A)). Qed.
Lemma lem1204231 {A : Type'} : (term10 A) = (term32 A).
Proof. exact (TRANS (@lem1204092 A) (@lem1204168 A)). Qed.
Lemma lem1204232 {A : Type'} : (term32 A) = (term10 A).
Proof. exact (SYM (@lem1204231 A)). Qed.
Lemma lem1204233 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem1204234 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem1204236 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem1204238 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem1204246 {A : Type'} (l : list A) : (term45 A l) = (term46 A l).
Proof. exact (@lem17362 (term47 A l) ((term48 A l) = (@LAST A l))). Qed.
Lemma lem1204247 {A : Type'} (P : type1143 A) : (term49 A P) = (term50 A P).
Proof. exact (@lem18392 (list A) P). Qed.
Lemma lem1204248 {A : Type'} : (term3 A) = (term51 A).
Proof. exact (@lem1204247 A (term44 A)). Qed.
Lemma lem1204249 {A : Type'} (l : list A) : (term52 A l) = (term43 A l).
Proof. exact (eq_refl (term52 A l)). Qed.
Lemma lem1204250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1204251 {A : Type'} (l : list A) : (term53 A l) = (term45 A l).
Proof. exact (MK_COMB (@lem1204250) (@lem1204249 A l)). Qed.
Lemma lem1204252 {A : Type'} (l : list A) : (term53 A l) = (term46 A l).
Proof. exact (TRANS (@lem1204251 A l) (@lem1204246 A l)). Qed.
Lemma lem1204253 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (fun_ext (fun l : list A => @lem1204252 A l)). Qed.
Lemma lem1204254 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1204255 {A : Type'} : (term51 A) = (term56 A).
Proof. exact (MK_COMB (@lem1204254 A) (@lem1204253 A)). Qed.
Lemma lem1204308 {A : Type'} : (term3 A) = (term56 A).
Proof. exact (TRANS (@lem1204248 A) (@lem1204255 A)). Qed.
Lemma lem1204309 {A : Type'} (h1 : term3 A) : term56 A.
Proof. exact (EQ_MP (@lem1204308 A) (@lem1204233 A h1)). Qed.
Lemma lem1204324 {A : Type'} (l : list A) : (((@List.rev A l) = (@nil A)) = (l = (@nil A))) = (term57 A l).
Proof. exact (@lem17784 ((@List.rev A l) = (@nil A)) (l = (@nil A))). Qed.
Lemma lem1204325 {A : Type'} : (term42 A) = (term58 A).
Proof. exact (fun_ext (fun l : list A => @lem1204324 A l)). Qed.
Lemma lem1204326 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204327 {A : Type'} : (term8 A) = (term59 A).
Proof. exact (MK_COMB (@lem1204326 A) (@lem1204325 A)). Qed.
Lemma lem1204329 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term60 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1204330 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term62 A P Q) = (term63 A P Q).
Proof. exact (@lem1204329 (list A) P Q). Qed.
Lemma lem1204331 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (@lem1204330 A (term66 A) (term67 A)). Qed.
Lemma lem1204332 {A : Type'} (l : list A) : (term68 A l) = (term69 A l).
Proof. exact (eq_refl (term68 A l)). Qed.
Lemma lem1204333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1204334 {A : Type'} (l : list A) : (term70 A l) = (term71 A l).
Proof. exact (MK_COMB (@lem1204333) (@lem1204332 A l)). Qed.
Lemma lem1204335 {A : Type'} (l : list A) : (term72 A l) = (term73 A l).
Proof. exact (eq_refl (term72 A l)). Qed.
Lemma lem1204336 {A : Type'} (l : list A) : (term74 A l) = (term57 A l).
Proof. exact (MK_COMB (@lem1204334 A l) (@lem1204335 A l)). Qed.
Lemma lem1204337 {A : Type'} : (term75 A) = (term58 A).
Proof. exact (fun_ext (fun l : list A => @lem1204336 A l)). Qed.
Lemma lem1204338 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204339 {A : Type'} : (term64 A) = (term59 A).
Proof. exact (MK_COMB (@lem1204338 A) (@lem1204337 A)). Qed.
Lemma lem1204340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1204341 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (MK_COMB (@lem1204340) (@lem1204339 A)). Qed.
Lemma lem1204342 {A : Type'} (l : list A) : (term68 A l) = (term69 A l).
Proof. exact (eq_refl (term68 A l)). Qed.
Lemma lem1204343 {A : Type'} : (term78 A) = (term66 A).
Proof. exact (fun_ext (fun l : list A => @lem1204342 A l)). Qed.
Lemma lem1204344 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204345 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (MK_COMB (@lem1204344 A) (@lem1204343 A)). Qed.
Lemma lem1204346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1204347 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem1204346) (@lem1204345 A)). Qed.
Lemma lem1204348 {A : Type'} (l : list A) : (term72 A l) = (term73 A l).
Proof. exact (eq_refl (term72 A l)). Qed.
Lemma lem1204349 {A : Type'} : (term83 A) = (term67 A).
Proof. exact (fun_ext (fun l : list A => @lem1204348 A l)). Qed.
Lemma lem1204350 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204351 {A : Type'} : (term84 A) = (term85 A).
Proof. exact (MK_COMB (@lem1204350 A) (@lem1204349 A)). Qed.
Lemma lem1204352 {A : Type'} : (term65 A) = (term86 A).
Proof. exact (MK_COMB (@lem1204347 A) (@lem1204351 A)). Qed.
Lemma lem1204353 {A : Type'} : ((term64 A) = (term65 A)) = ((term59 A) = (term86 A)).
Proof. exact (MK_COMB (@lem1204341 A) (@lem1204352 A)). Qed.
Lemma lem1204452 {A : Type'} : (term59 A) = (term86 A).
Proof. exact (EQ_MP (@lem1204353 A) (@lem1204331 A)). Qed.
Lemma lem1204453 {A : Type'} : (term8 A) = (term86 A).
Proof. exact (TRANS (@lem1204327 A) (@lem1204452 A)). Qed.
Lemma lem1204454 {A : Type'} (h1 : term8 A) : term86 A.
Proof. exact (EQ_MP (@lem1204453 A) (@lem1204234 A h1)). Qed.
Lemma lem1204600 {A : Type'} (l : list A) : ((term39 A l) = l) = ((term39 A l) = l).
Proof. exact (eq_refl ((term39 A l) = l)). Qed.
Lemma lem1204601 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun l : list A => @lem1204600 A l)). Qed.
Lemma lem1204602 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204611 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1204602 A) (@lem1204601 A)). Qed.
Lemma lem1204612 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1204611 A) (@lem1204236 A h1)). Qed.
Lemma lem1204628 {A : Type'} (l : list A) : (term87 A l) = (l = (@nil A)).
Proof. exact (@lem16933 (l = (@nil A))). Qed.
Lemma lem1204629 {A : Type'} (l : list A) : ((term88 A l) = (@hd A l)) = ((term88 A l) = (@hd A l)).
Proof. exact (eq_refl ((term88 A l) = (@hd A l))). Qed.
Lemma lem1204630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1204631 {A : Type'} (l : list A) : (term89 A l) = (term90 A l).
Proof. exact (MK_COMB (@lem1204630) (@lem1204628 A l)). Qed.
Lemma lem1204632 {A : Type'} (l : list A) : (term91 A l) = (term92 A l).
Proof. exact (MK_COMB (@lem1204631 A l) (@lem1204629 A l)). Qed.
Lemma lem1204633 {A : Type'} (l : list A) : (term35 A l) = (term91 A l).
Proof. exact (@lem17265 (term47 A l) ((term88 A l) = (@hd A l))). Qed.
Lemma lem1204634 {A : Type'} (l : list A) : (term35 A l) = (term92 A l).
Proof. exact (TRANS (@lem1204633 A l) (@lem1204632 A l)). Qed.
Lemma lem1204635 {A : Type'} : (term36 A) = (term93 A).
Proof. exact (fun_ext (fun l : list A => @lem1204634 A l)). Qed.
Lemma lem1204636 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204689 {A : Type'} : (term4 A) = (term94 A).
Proof. exact (MK_COMB (@lem1204636 A) (@lem1204635 A)). Qed.
Lemma lem1204690 {A : Type'} (h1 : term4 A) : term94 A.
Proof. exact (EQ_MP (@lem1204689 A) (@lem1204238 A h1)). Qed.
Lemma lem1204773 {A : Type'} (l : list A) : (term73 A l) = (term73 A l).
Proof. exact (eq_refl (term73 A l)). Qed.
Lemma lem1204774 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (fun_ext (fun l : list A => @lem1204773 A l)). Qed.
Lemma lem1204775 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204776 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (MK_COMB (@lem1204775 A) (@lem1204774 A)). Qed.
Lemma lem1204793 {A : Type'} (l : list A) : (term69 A l) = (term69 A l).
Proof. exact (eq_refl (term69 A l)). Qed.
Lemma lem1204794 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (fun_ext (fun l : list A => @lem1204793 A l)). Qed.
Lemma lem1204795 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204796 {A : Type'} : (term80 A) = (term80 A).
Proof. exact (MK_COMB (@lem1204795 A) (@lem1204794 A)). Qed.
Lemma lem1204797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1204798 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (MK_COMB (@lem1204797) (@lem1204796 A)). Qed.
Lemma lem1204799 {A : Type'} : (term86 A) = (term86 A).
Proof. exact (MK_COMB (@lem1204798 A) (@lem1204776 A)). Qed.
Lemma lem1204800 {A : Type'} (h1 : term8 A) : term86 A.
Proof. exact (EQ_MP (@lem1204799 A) (@lem1204454 A h1)). Qed.
Lemma lem1204853 {A : Type'} (l : list A) : ((term39 A l) = l) = ((term39 A l) = l).
Proof. exact (eq_refl ((term39 A l) = l)). Qed.
Lemma lem1204854 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun l : list A => @lem1204853 A l)). Qed.
Lemma lem1204855 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204856 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1204855 A) (@lem1204854 A)). Qed.
Lemma lem1204857 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1204856 A) (@lem1204612 A h1)). Qed.
Lemma lem1204889 {A : Type'} (l : list A) : (term92 A l) = (term92 A l).
Proof. exact (eq_refl (term92 A l)). Qed.
Lemma lem1204890 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (fun_ext (fun l : list A => @lem1204889 A l)). Qed.
Lemma lem1204891 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204892 {A : Type'} : (term94 A) = (term94 A).
Proof. exact (MK_COMB (@lem1204891 A) (@lem1204890 A)). Qed.
Lemma lem1204893 {A : Type'} (h1 : term4 A) : term94 A.
Proof. exact (EQ_MP (@lem1204892 A) (@lem1204690 A h1)). Qed.
Lemma lem1204940 {A : Type'} (l : list A) (h1 : term46 A l) : term46 A l.
Proof. exact (h1). Qed.
Lemma lem1204945 {A : Type'} (h1 : term8 A) : term85 A.
Proof. exact (proj2 (@lem1204800 A h1)). Qed.
Lemma lem1204948 {A : Type'} (l : list A) : ((term39 A l) = l) = ((term39 A l) = l).
Proof. exact (eq_refl ((term39 A l) = l)). Qed.
Lemma lem1204949 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun l : list A => @lem1204948 A l)). Qed.
Lemma lem1204950 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204952 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1204950 A) (@lem1204949 A)). Qed.
Lemma lem1204953 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1204952 A) (@lem1204857 A h1)). Qed.
Lemma lem1204968 {A : Type'} (l : list A) : (term92 A l) = (term92 A l).
Proof. exact (eq_refl (term92 A l)). Qed.
Lemma lem1204969 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (fun_ext (fun l : list A => @lem1204968 A l)). Qed.
Lemma lem1204970 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1204972 {A : Type'} : (term94 A) = (term94 A).
Proof. exact (MK_COMB (@lem1204970 A) (@lem1204969 A)). Qed.
Lemma lem1204973 {A : Type'} (h1 : term4 A) : term94 A.
Proof. exact (EQ_MP (@lem1204972 A) (@lem1204893 A h1)). Qed.
Lemma lem1205041 {A : Type'} (l : list A) : (term73 A l) = (term73 A l).
Proof. exact (eq_refl (term73 A l)). Qed.
Lemma lem1205042 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (fun_ext (fun l : list A => @lem1205041 A l)). Qed.
Lemma lem1205043 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1205045 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (MK_COMB (@lem1205043 A) (@lem1205042 A)). Qed.
Lemma lem1205046 {A : Type'} (h1 : term8 A) : term85 A.
Proof. exact (EQ_MP (@lem1205045 A) (@lem1204945 A h1)). Qed.
Lemma lem1205047 {A : Type'} (_21628 : list A) (h1 : term6 A) : term95 A _21628.
Proof. exact (@lem1204953 A h1 _21628). Qed.
Lemma lem1205048 {A : Type'} (_21628 : list A) : (term95 A _21628) = ((term39 A _21628) = _21628).
Proof. exact (eq_refl (term95 A _21628)). Qed.
Lemma lem1205053 {A : Type'} (_21630 : list A) (h1 : term4 A) : term96 A _21630.
Proof. exact (@lem1204973 A h1 _21630). Qed.
Lemma lem1205054 {A : Type'} (_21630 : list A) : (term96 A _21630) = (term92 A _21630).
Proof. exact (eq_refl (term96 A _21630)). Qed.
Lemma lem1205068 {A : Type'} (_21635 : list A) (h1 : term8 A) : term72 A _21635.
Proof. exact (@lem1205046 A h1 _21635). Qed.
Lemma lem1205069 {A : Type'} (_21635 : list A) : (term72 A _21635) = (term73 A _21635).
Proof. exact (eq_refl (term72 A _21635)). Qed.
Lemma lem1205080 {A : Type'} (_21630 : list A) (h1 : term4 A) : term92 A _21630.
Proof. exact (EQ_MP (@lem1205054 A _21630) (@lem1205053 A _21630 h1)). Qed.
Lemma lem1205090 {A : Type'} (l : list A) (h1 : term46 A l) : term97 A l.
Proof. exact (proj2 (@lem1204940 A l h1)). Qed.
Lemma lem1205114 {A : Type'} (_21635 : list A) (h1 : term8 A) : term73 A _21635.
Proof. exact (EQ_MP (@lem1205069 A _21635) (@lem1205068 A _21635 h1)). Qed.
Lemma lem1205131 {A : Type'} : (@LAST A) = (@LAST A).
Proof. exact (eq_refl (@LAST A)). Qed.
Lemma lem1205132 {A : Type'} (_21640 : list A) (_21641 : list A) (h1 : _21640 = _21641) : _21640 = _21641.
Proof. exact (h1). Qed.
Lemma lem1205133 {A : Type'} (_21640 : list A) (_21641 : list A) (h1 : _21640 = _21641) : (@LAST A _21640) = (@LAST A _21641).
Proof. exact (MK_COMB (@lem1205131 A) (@lem1205132 A _21640 _21641 h1)). Qed.
Lemma lem1205134 {A : Type'} (_21640 : list A) (_21641 : list A) : term98 A _21640 _21641.
Proof. exact (fun h0 : _21640 = _21641 => @lem1205133 A _21640 _21641 h0). Qed.
Lemma lem1205136 (a : Prop) (b : Prop) : (a -> b) = (term99 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1205137 {A : Type'} (_21640 : list A) (_21641 : list A) : (term98 A _21640 _21641) = (term100 A _21640 _21641).
Proof. exact (@lem1205136 (_21640 = _21641) ((@LAST A _21640) = (@LAST A _21641))). Qed.
Lemma lem1205138 {A : Type'} (_21640 : list A) (_21641 : list A) : term100 A _21640 _21641.
Proof. exact (EQ_MP (@lem1205137 A _21640 _21641) (@lem1205134 A _21640 _21641)). Qed.
Lemma lem1205168 {A : Type'} (x : A) (y : A) (z : A) : term101 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1205170 {A : Type'} (l : list A) (h1 : term46 A l) : term47 A l.
Proof. exact (proj1 (@lem1204940 A l h1)). Qed.
Lemma lem1205171 {A : Type'} (l : list A) (h1 : term46 A l) : term102 A l.
Proof. exact (fun h0 : l = (@nil A) => @lem1205170 A l h1). Qed.
Lemma lem1205173 (p : Prop) : (term103 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1205174 {A : Type'} (l : list A) : (term102 A l) = (term47 A l).
Proof. exact (@lem1205173 (l = (@nil A))). Qed.
Lemma lem1205175 {A : Type'} (l : list A) (h1 : term46 A l) : term47 A l.
Proof. exact (EQ_MP (@lem1205174 A l) (@lem1205171 A l h1)). Qed.
Lemma lem1205177 (b : Prop) (a : Prop) : (a \/ b) = (term104 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1205180 {A : Type'} (_21635 : list A) : (term73 A _21635) = (term105 A _21635).
Proof. exact (@lem1205177 (_21635 = (@nil A)) (term106 A _21635)). Qed.
Lemma lem1205183 {A : Type'} (_21635 : list A) (h1 : term8 A) : term105 A _21635.
Proof. exact (EQ_MP (@lem1205180 A _21635) (@lem1205114 A _21635 h1)). Qed.
Lemma lem1205184 {A : Type'} (_21635 : list A) (h1 : term8 A) : term105 A _21635.
Proof. exact (@lem1205183 A _21635 h1). Qed.
Lemma lem1205185 {A : Type'} (l : list A) (h1 : term8 A) : term105 A l.
Proof. exact (@lem1205184 A l h1). Qed.
Lemma lem1205188 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term46 A l) : term106 A l.
Proof. exact (@lem1205185 A l h1 (@lem1205175 A l h2)). Qed.
Lemma lem1205189 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term46 A l) : term107 A l.
Proof. exact (fun h0 : (@List.rev A l) = (@nil A) => @lem1205188 A l h1 h2). Qed.
Lemma lem1205191 (p : Prop) : (term103 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1205192 {A : Type'} (l : list A) : (term107 A l) = (term106 A l).
Proof. exact (@lem1205191 ((@List.rev A l) = (@nil A))). Qed.
Lemma lem1205193 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term46 A l) : term106 A l.
Proof. exact (EQ_MP (@lem1205192 A l) (@lem1205189 A l h1 h2)). Qed.
Lemma lem1205199 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1205200 {A : Type'} (_21630 : list A) : (term92 A _21630) = (term108 A _21630).
Proof. exact (@lem1205199 ((term88 A _21630) = (@hd A _21630)) (_21630 = (@nil A))). Qed.
Lemma lem1205210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1205211 {A : Type'} (_21630 : list A) : (term109 A _21630) = (term110 A _21630).
Proof. exact (MK_COMB (@lem1205210) (@lem1205200 A _21630)). Qed.
Lemma lem1205221 {A : Type'} (_21630 : list A) : (term108 A _21630) = (term108 A _21630).
Proof. exact (eq_refl (term108 A _21630)). Qed.
Lemma lem1205222 {A : Type'} (_21630 : list A) : ((term92 A _21630) = (term108 A _21630)) = ((term108 A _21630) = (term108 A _21630)).
Proof. exact (MK_COMB (@lem1205211 A _21630) (@lem1205221 A _21630)). Qed.
Lemma lem1205224 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1205225 (x : Prop) : (x = x) = True.
Proof. exact (@lem1205224 Prop x). Qed.
Lemma lem1205226 {A : Type'} (_21630 : list A) : ((term108 A _21630) = (term108 A _21630)) = True.
Proof. exact (@lem1205225 (term108 A _21630)). Qed.
Lemma lem1205227 {A : Type'} (_21630 : list A) : ((term92 A _21630) = (term108 A _21630)) = True.
Proof. exact (TRANS (@lem1205222 A _21630) (@lem1205226 A _21630)). Qed.
Lemma lem1205228 {A : Type'} (_21630 : list A) : True = ((term92 A _21630) = (term108 A _21630)).
Proof. exact (SYM (@lem1205227 A _21630)). Qed.
Lemma lem1205229 {A : Type'} (_21630 : list A) : (term92 A _21630) = (term108 A _21630).
Proof. exact (EQ_MP (@lem1205228 A _21630) (@lem0)). Qed.
Lemma lem1205230 {A : Type'} (_21630 : list A) (h1 : term4 A) : term108 A _21630.
Proof. exact (EQ_MP (@lem1205229 A _21630) (@lem1205080 A _21630 h1)). Qed.
Lemma lem1205232 (b : Prop) (a : Prop) : (a \/ b) = (term104 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1205235 {A : Type'} (_21630 : list A) : (term108 A _21630) = (term35 A _21630).
Proof. exact (@lem1205232 (_21630 = (@nil A)) ((term88 A _21630) = (@hd A _21630))). Qed.
Lemma lem1205238 {A : Type'} (_21630 : list A) (h1 : term4 A) : term35 A _21630.
Proof. exact (EQ_MP (@lem1205235 A _21630) (@lem1205230 A _21630 h1)). Qed.
Lemma lem1205239 {A : Type'} (_21630 : list A) (h1 : term4 A) : term35 A _21630.
Proof. exact (@lem1205238 A _21630 h1). Qed.
Lemma lem1205240 {A : Type'} (l : list A) (h1 : term4 A) : term111 A l.
Proof. exact (@lem1205239 A (@List.rev A l) h1). Qed.
Lemma lem1205243 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term4 A) (h3 : term46 A l) : (term112 A l) = (term48 A l).
Proof. exact (@lem1205240 A l h2 (@lem1205193 A l h1 h3)). Qed.
Lemma lem1205244 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term4 A) (h3 : term46 A l) : term113 A l.
Proof. exact (fun h0 : term114 A l => @lem1205243 A l h1 h2 h3). Qed.
Lemma lem1205246 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1205247 {A : Type'} (l : list A) : (term113 A l) = ((term112 A l) = (term48 A l)).
Proof. exact (@lem1205246 ((term112 A l) = (term48 A l))). Qed.
Lemma lem1205248 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term4 A) (h3 : term46 A l) : (term112 A l) = (term48 A l).
Proof. exact (EQ_MP (@lem1205247 A l) (@lem1205244 A l h1 h2 h3)). Qed.
Lemma lem1205250 {A : Type'} (_21628 : list A) (h1 : term6 A) : (term39 A _21628) = _21628.
Proof. exact (EQ_MP (@lem1205048 A _21628) (@lem1205047 A _21628 h1)). Qed.
Lemma lem1205251 {A : Type'} (_21628 : list A) (h1 : term6 A) : (term39 A _21628) = _21628.
Proof. exact (@lem1205250 A _21628 h1). Qed.
Lemma lem1205252 {A : Type'} (l : list A) (h1 : term6 A) : (term39 A l) = l.
Proof. exact (@lem1205251 A l h1). Qed.
Lemma lem1205253 {A : Type'} (l : list A) (h1 : term6 A) : term116 A l.
Proof. exact (fun h0 : term117 A l => @lem1205252 A l h1). Qed.
Lemma lem1205255 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1205256 {A : Type'} (l : list A) : (term116 A l) = ((term39 A l) = l).
Proof. exact (@lem1205255 ((term39 A l) = l)). Qed.
Lemma lem1205257 {A : Type'} (l : list A) (h1 : term6 A) : (term39 A l) = l.
Proof. exact (EQ_MP (@lem1205256 A l) (@lem1205253 A l h1)). Qed.
Lemma lem1205263 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1205264 {A : Type'} (_21640 : list A) (_21641 : list A) : (term100 A _21640 _21641) = (term118 A _21640 _21641).
Proof. exact (@lem1205263 ((@LAST A _21640) = (@LAST A _21641)) (term119 A _21640 _21641)). Qed.
Lemma lem1205274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1205275 {A : Type'} (_21640 : list A) (_21641 : list A) : (term120 A _21640 _21641) = (term121 A _21640 _21641).
Proof. exact (MK_COMB (@lem1205274) (@lem1205264 A _21640 _21641)). Qed.
Lemma lem1205285 {A : Type'} (_21640 : list A) (_21641 : list A) : (term118 A _21640 _21641) = (term118 A _21640 _21641).
Proof. exact (eq_refl (term118 A _21640 _21641)). Qed.
Lemma lem1205286 {A : Type'} (_21640 : list A) (_21641 : list A) : ((term100 A _21640 _21641) = (term118 A _21640 _21641)) = ((term118 A _21640 _21641) = (term118 A _21640 _21641)).
Proof. exact (MK_COMB (@lem1205275 A _21640 _21641) (@lem1205285 A _21640 _21641)). Qed.
Lemma lem1205288 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1205289 (x : Prop) : (x = x) = True.
Proof. exact (@lem1205288 Prop x). Qed.
Lemma lem1205290 {A : Type'} (_21640 : list A) (_21641 : list A) : ((term118 A _21640 _21641) = (term118 A _21640 _21641)) = True.
Proof. exact (@lem1205289 (term118 A _21640 _21641)). Qed.
Lemma lem1205291 {A : Type'} (_21640 : list A) (_21641 : list A) : ((term100 A _21640 _21641) = (term118 A _21640 _21641)) = True.
Proof. exact (TRANS (@lem1205286 A _21640 _21641) (@lem1205290 A _21640 _21641)). Qed.
Lemma lem1205292 {A : Type'} (_21640 : list A) (_21641 : list A) : True = ((term100 A _21640 _21641) = (term118 A _21640 _21641)).
Proof. exact (SYM (@lem1205291 A _21640 _21641)). Qed.
Lemma lem1205293 {A : Type'} (_21640 : list A) (_21641 : list A) : (term100 A _21640 _21641) = (term118 A _21640 _21641).
Proof. exact (EQ_MP (@lem1205292 A _21640 _21641) (@lem0)). Qed.
Lemma lem1205294 {A : Type'} (_21640 : list A) (_21641 : list A) : term118 A _21640 _21641.
Proof. exact (EQ_MP (@lem1205293 A _21640 _21641) (@lem1205138 A _21640 _21641)). Qed.
Lemma lem1205296 (b : Prop) (a : Prop) : (a \/ b) = (term104 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1205297 {A : Type'} (_21640 : list A) (_21641 : list A) : (term118 A _21640 _21641) = (term122 A _21640 _21641).
Proof. exact (@lem1205296 (term119 A _21640 _21641) ((@LAST A _21640) = (@LAST A _21641))). Qed.
Lemma lem1205299 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1205300 {A : Type'} (_21640 : list A) (_21641 : list A) : (term124 A _21640 _21641) = (_21640 = _21641).
Proof. exact (@lem1205299 (_21640 = _21641)). Qed.
Lemma lem1205301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205302 {A : Type'} (_21640 : list A) (_21641 : list A) : (term125 A _21640 _21641) = (term126 A _21640 _21641).
Proof. exact (MK_COMB (@lem1205301) (@lem1205300 A _21640 _21641)). Qed.
Lemma lem1205303 {A : Type'} (_21640 : list A) (_21641 : list A) : ((@LAST A _21640) = (@LAST A _21641)) = ((@LAST A _21640) = (@LAST A _21641)).
Proof. exact (eq_refl ((@LAST A _21640) = (@LAST A _21641))). Qed.
Lemma lem1205304 {A : Type'} (_21640 : list A) (_21641 : list A) : (term122 A _21640 _21641) = (term98 A _21640 _21641).
Proof. exact (MK_COMB (@lem1205302 A _21640 _21641) (@lem1205303 A _21640 _21641)). Qed.
Lemma lem1205305 {A : Type'} (_21640 : list A) (_21641 : list A) : (term118 A _21640 _21641) = (term98 A _21640 _21641).
Proof. exact (TRANS (@lem1205297 A _21640 _21641) (@lem1205304 A _21640 _21641)). Qed.
Lemma lem1205308 {A : Type'} (_21640 : list A) (_21641 : list A) : term98 A _21640 _21641.
Proof. exact (EQ_MP (@lem1205305 A _21640 _21641) (@lem1205294 A _21640 _21641)). Qed.
Lemma lem1205309 {A : Type'} (_21640 : list A) (_21641 : list A) : term98 A _21640 _21641.
Proof. exact (@lem1205308 A _21640 _21641). Qed.
Lemma lem1205310 {A : Type'} (l : list A) : term127 A l.
Proof. exact (@lem1205309 A (term39 A l) l). Qed.
Lemma lem1205313 {A : Type'} (l : list A) (h1 : term6 A) : (term112 A l) = (@LAST A l).
Proof. exact (@lem1205310 A l (@lem1205257 A l h1)). Qed.
Lemma lem1205314 {A : Type'} (l : list A) (h1 : term6 A) : (term112 A l) = (@LAST A l).
Proof. exact (@lem1205313 A l h1). Qed.
Lemma lem1205315 {A : Type'} (l : list A) (h1 : term6 A) : term128 A l.
Proof. exact (fun h0 : term129 A l => @lem1205314 A l h1). Qed.
Lemma lem1205317 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1205318 {A : Type'} (l : list A) : (term128 A l) = ((term112 A l) = (@LAST A l)).
Proof. exact (@lem1205317 ((term112 A l) = (@LAST A l))). Qed.
Lemma lem1205319 {A : Type'} (l : list A) (h1 : term6 A) : (term112 A l) = (@LAST A l).
Proof. exact (EQ_MP (@lem1205318 A l) (@lem1205315 A l h1)). Qed.
Lemma lem1205337 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1205338 {A : Type'} (y : A) (x : A) (z : A) : (term130 A x y z) = (term131 A y x z).
Proof. exact (@lem1205337 (y = z) (term132 A x z)). Qed.
Lemma lem1205348 {A : Type'} (x : A) (y : A) : (term133 A x y) = (term133 A x y).
Proof. exact (eq_refl (term133 A x y)). Qed.
Lemma lem1205349 {A : Type'} (y : A) (x : A) (z : A) : (term101 A x y z) = (term134 A y x z).
Proof. exact (MK_COMB (@lem1205348 A x y) (@lem1205338 A y x z)). Qed.
Lemma lem1205353 (q : Prop) (p : Prop) (r : Prop) : (term135 p q r) = (term135 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1205354 {A : Type'} (y : A) (x : A) (z : A) : (term134 A y x z) = (term136 A y x z).
Proof. exact (@lem1205353 (y = z) (term132 A x y) (term132 A x z)). Qed.
Lemma lem1205376 {A : Type'} (y : A) (x : A) (z : A) : (term101 A x y z) = (term136 A y x z).
Proof. exact (TRANS (@lem1205349 A y x z) (@lem1205354 A y x z)). Qed.
Lemma lem1205377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1205378 {A : Type'} (y : A) (x : A) (z : A) : (term137 A x y z) = (term138 A y x z).
Proof. exact (MK_COMB (@lem1205377) (@lem1205376 A y x z)). Qed.
Lemma lem1205400 {A : Type'} (y : A) (x : A) (z : A) : (term136 A y x z) = (term136 A y x z).
Proof. exact (eq_refl (term136 A y x z)). Qed.
Lemma lem1205401 {A : Type'} (y : A) (x : A) (z : A) : ((term101 A x y z) = (term136 A y x z)) = ((term136 A y x z) = (term136 A y x z)).
Proof. exact (MK_COMB (@lem1205378 A y x z) (@lem1205400 A y x z)). Qed.
Lemma lem1205403 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1205404 (x : Prop) : (x = x) = True.
Proof. exact (@lem1205403 Prop x). Qed.
Lemma lem1205405 {A : Type'} (y : A) (x : A) (z : A) : ((term136 A y x z) = (term136 A y x z)) = True.
Proof. exact (@lem1205404 (term136 A y x z)). Qed.
Lemma lem1205406 {A : Type'} (y : A) (x : A) (z : A) : ((term101 A x y z) = (term136 A y x z)) = True.
Proof. exact (TRANS (@lem1205401 A y x z) (@lem1205405 A y x z)). Qed.
Lemma lem1205407 {A : Type'} (y : A) (x : A) (z : A) : True = ((term101 A x y z) = (term136 A y x z)).
Proof. exact (SYM (@lem1205406 A y x z)). Qed.
Lemma lem1205408 {A : Type'} (y : A) (x : A) (z : A) : (term101 A x y z) = (term136 A y x z).
Proof. exact (EQ_MP (@lem1205407 A y x z) (@lem0)). Qed.
Lemma lem1205409 {A : Type'} (y : A) (x : A) (z : A) : term136 A y x z.
Proof. exact (EQ_MP (@lem1205408 A y x z) (@lem1205168 A x y z)). Qed.
Lemma lem1205411 (b : Prop) (a : Prop) : (a \/ b) = (term104 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1205412 {A : Type'} (x : A) (y : A) (z : A) : (term136 A y x z) = (term139 A x y z).
Proof. exact (@lem1205411 (term140 A y x z) (y = z)). Qed.
Lemma lem1205414 (a : Prop) (b : Prop) : (term141 a b) = (term142 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1205415 {A : Type'} (y : A) (x : A) (z : A) : (term143 A y x z) = (term144 A y x z).
Proof. exact (@lem1205414 (term132 A x y) (term132 A x z)). Qed.
Lemma lem1205417 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1205418 {A : Type'} (x : A) (y : A) : (term145 A x y) = (x = y).
Proof. exact (@lem1205417 (x = y)). Qed.
Lemma lem1205419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1205420 {A : Type'} (x : A) (y : A) : (term146 A x y) = (term147 A x y).
Proof. exact (MK_COMB (@lem1205419) (@lem1205418 A x y)). Qed.
Lemma lem1205422 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1205423 {A : Type'} (x : A) (z : A) : (term145 A x z) = (x = z).
Proof. exact (@lem1205422 (x = z)). Qed.
Lemma lem1205424 {A : Type'} (y : A) (x : A) (z : A) : (term144 A y x z) = (term148 A y x z).
Proof. exact (MK_COMB (@lem1205420 A x y) (@lem1205423 A x z)). Qed.
Lemma lem1205425 {A : Type'} (y : A) (x : A) (z : A) : (term143 A y x z) = (term148 A y x z).
Proof. exact (TRANS (@lem1205415 A y x z) (@lem1205424 A y x z)). Qed.
Lemma lem1205426 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1205427 {A : Type'} (y : A) (x : A) (z : A) : (term149 A y x z) = (term150 A y x z).
Proof. exact (MK_COMB (@lem1205426) (@lem1205425 A y x z)). Qed.
Lemma lem1205428 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1205429 {A : Type'} (x : A) (y : A) (z : A) : (term139 A x y z) = (term151 A x y z).
Proof. exact (MK_COMB (@lem1205427 A y x z) (@lem1205428 A y z)). Qed.
Lemma lem1205430 {A : Type'} (x : A) (y : A) (z : A) : (term136 A y x z) = (term151 A x y z).
Proof. exact (TRANS (@lem1205412 A x y z) (@lem1205429 A x y z)). Qed.
Lemma lem1205432 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : term152 A l.
Proof. exact (conj (@lem1205248 A l h1 h3 h4) (@lem1205319 A l h2)). Qed.
Lemma lem1205434 {A : Type'} (x : A) (y : A) (z : A) : term151 A x y z.
Proof. exact (EQ_MP (@lem1205430 A x y z) (@lem1205409 A y x z)). Qed.
Lemma lem1205435 {A : Type'} (x : A) (y : A) (z : A) : term151 A x y z.
Proof. exact (@lem1205434 A x y z). Qed.
Lemma lem1205436 {A : Type'} (l : list A) : term153 A l.
Proof. exact (@lem1205435 A (term112 A l) (term48 A l) (@LAST A l)). Qed.
Lemma lem1205439 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : (term48 A l) = (@LAST A l).
Proof. exact (@lem1205436 A l (@lem1205432 A l h1 h2 h3 h4)). Qed.
Lemma lem1205440 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : term154 A l.
Proof. exact (fun h0 : term97 A l => @lem1205439 A l h1 h2 h3 h4). Qed.
Lemma lem1205442 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1205443 {A : Type'} (l : list A) : (term154 A l) = ((term48 A l) = (@LAST A l)).
Proof. exact (@lem1205442 ((term48 A l) = (@LAST A l))). Qed.
Lemma lem1205444 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : (term48 A l) = (@LAST A l).
Proof. exact (EQ_MP (@lem1205443 A l) (@lem1205440 A l h1 h2 h3 h4)). Qed.
Lemma lem1205447 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1205449 {A : Type'} (l : list A) : (term97 A l) = (term155 A l).
Proof. exact (@lem1205447 ((term48 A l) = (@LAST A l))). Qed.
Lemma lem1205452 {A : Type'} (l : list A) (h1 : term46 A l) : term155 A l.
Proof. exact (EQ_MP (@lem1205449 A l) (@lem1205090 A l h1)). Qed.
Lemma lem1205455 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : False.
Proof. exact (@lem1205452 A l h4 (@lem1205444 A l h1 h2 h3 h4)). Qed.
Lemma lem1205456 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : term156.
Proof. exact (fun h0 : ~ False => @lem1205455 A l h1 h2 h3 h4). Qed.
Lemma lem1205458 (p : Prop) : (term115 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1205459 : term156 = False.
Proof. exact (@lem1205458 False). Qed.
Lemma lem1205460 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : False.
Proof. exact (EQ_MP (@lem1205459) (@lem1205456 A l h1 h2 h3 h4)). Qed.
Lemma lem1205461 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : (term6 A) = False.
Proof. exact (prop_ext (fun h5 : term6 A => @lem1205460 A l h1 h2 h3 h4) (fun h5 : False => @lem1204953 A h2)). Qed.
Lemma lem1205462 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : False.
Proof. exact (EQ_MP (@lem1205461 A l h1 h2 h3 h4) (@lem1204953 A h2)). Qed.
Lemma lem1205463 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : (term46 A l) = False.
Proof. exact (prop_ext (fun h5 : term46 A l => @lem1205462 A l h1 h2 h3 h4) (fun h5 : False => @lem1204940 A l h4)). Qed.
Lemma lem1205464 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : False.
Proof. exact (EQ_MP (@lem1205463 A l h1 h2 h3 h4) (@lem1204940 A l h4)). Qed.
Lemma lem1205465 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : (term6 A) = False.
Proof. exact (prop_ext (fun h5 : term6 A => @lem1205464 A l h1 h2 h3 h4) (fun h5 : False => @lem1204857 A h2)). Qed.
Lemma lem1205466 {A : Type'} (l : list A) (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term46 A l) : False.
Proof. exact (EQ_MP (@lem1205465 A l h1 h2 h3 h4) (@lem1204857 A h2)). Qed.
Lemma lem1205467 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term3 A) : False.
Proof. exact (ex_elim (@lem1204309 A h4) (fun l : list A => fun h0 : term55 A l => @lem1205466 A l h1 h2 h3 h0)). Qed.
Lemma lem1205468 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term3 A) : (term6 A) = False.
Proof. exact (prop_ext (fun h5 : term6 A => @lem1205467 A h1 h2 h3 h4) (fun h5 : False => @lem1204612 A h2)). Qed.
Lemma lem1205469 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term3 A) : False.
Proof. exact (EQ_MP (@lem1205468 A h1 h2 h3 h4) (@lem1204612 A h2)). Qed.
Lemma lem1205470 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term3 A) : term14 A.
Proof. exact (fun h0 : term5 A => @lem1205469 A h1 h2 h3 h4). Qed.
Lemma lem1205471 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (@lem69 (term5 A)). Qed.
Lemma lem1205472 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term4 A) (h4 : term3 A) : term15 A.
Proof. exact (EQ_MP (@lem1205471 A) (@lem1205470 A h1 h2 h3 h4)). Qed.
Lemma lem1205473 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term3 A) : term18 A.
Proof. exact (fun h0 : term4 A => @lem1205472 A h1 h2 h0 h3). Qed.
Lemma lem1205474 {A : Type'} (h1 : term8 A) (h2 : term6 A) (h3 : term3 A) : term21 A.
Proof. exact (fun h0 : term7 A => @lem1205473 A h1 h2 h3). Qed.
Lemma lem1205475 {A : Type'} (h1 : term8 A) (h2 : term3 A) : term24 A.
Proof. exact (fun h0 : term6 A => @lem1205474 A h1 h0 h2). Qed.
Lemma lem1205476 {A : Type'} (h1 : term8 A) (h2 : term3 A) : term27 A.
Proof. exact (fun h0 : term9 A => @lem1205475 A h1 h2). Qed.
Lemma lem1205477 {A : Type'} (h1 : term3 A) : term30 A.
Proof. exact (fun h0 : term8 A => @lem1205476 A h0 h1). Qed.
Lemma lem1205478 {A : Type'} : term32 A.
Proof. exact (fun h0 : term3 A => @lem1205477 A h0). Qed.
Lemma lem1205479 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem1204232 A) (@lem1205478 A)). Qed.
Lemma lem1205481 {A : Type'} : term10 A.
Proof. exact (@lem1204015 A (@lem1205479 A)). Qed.
Lemma lem1205482 {A : Type'} (h1 : term3 A) : term29 A.
Proof. exact (@lem1205481 A (@lem1203982 A h1)). Qed.
Lemma lem1205483 {A : Type'} (h1 : term3 A) : term26 A.
Proof. exact (@lem1205482 A h1 (@lem1203994 A)). Qed.
Lemma lem1205484 {A : Type'} (h1 : term3 A) : term23 A.
Proof. exact (@lem1205483 A h1 (@lem1203995 A)). Qed.
Lemma lem1205485 {A : Type'} (h1 : term3 A) : term20 A.
Proof. exact (@lem1205484 A h1 (@lem1203990 A)). Qed.
Lemma lem1205486 {A : Type'} (h1 : term3 A) : term17 A.
Proof. exact (@lem1205485 A h1 (@lem1203991 A)). Qed.
Lemma lem1205487 {A : Type'} (h1 : term3 A) : term14 A.
Proof. exact (@lem1205486 A h1 (@lem1203983 A)). Qed.
Lemma lem1205488 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem1205487 A h1 (@lem1203985 A)). Qed.
Lemma lem1205489 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem1205488 A h1) (fun h2 : False => @lem1203982 A h1)). Qed.
Lemma lem1205490 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem1205489 A h1) (@lem1203982 A h1)). Qed.
Lemma lem1205491 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem1205490 A h0). Qed.
Lemma lem1205492 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1203981 A) (@lem1205491 A)). Qed.
