Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318736_term_abbrevs.
Require Import NADD_COMPLETE_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import thm1317735_spec.
Require Import thm1317744_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm38926_spec.
Lemma lem1318240 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : P = (term0 Q).
Proof. exact (h1). Qed.
Lemma lem1318241 (x : nadd) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1318242 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (P x) = (term1 Q x).
Proof. exact (MK_COMB (@lem1318240 P Q h1) (@lem1318241 x)). Qed.
Lemma lem1318243 (Q : hreal -> Prop) (x : nadd) : (term1 Q x) = (term2 Q x).
Proof. exact (eq_refl (term1 Q x)). Qed.
Lemma lem1318244 (P : nadd -> Prop) (x : nadd) : (term3 P x) = (term3 P x).
Proof. exact (eq_refl (term3 P x)). Qed.
Lemma lem1318245 (P : nadd -> Prop) (Q : hreal -> Prop) (x : nadd) : ((P x) = (term1 Q x)) = ((P x) = (term2 Q x)).
Proof. exact (MK_COMB (@lem1318244 P x) (@lem1318243 Q x)). Qed.
Lemma lem1318247 (P : nadd -> Prop) : term4 P.
Proof. exact (@lem1299407 P). Qed.
Lemma lem1318248 (P : nadd -> Prop) : (term4 P) = (term5 P).
Proof. exact (eq_refl (term4 P)). Qed.
Lemma lem1318249 (P : nadd -> Prop) : term5 P.
Proof. exact (EQ_MP (@lem1318248 P) (@lem1318247 P)). Qed.
Lemma lem1318250 : term6.
Proof. exact (fun a : hreal => @lem1317735 a). Qed.
Lemma lem1318251 : term7.
Proof. exact (fun r : nadd -> Prop => @lem1317744 r). Qed.
Lemma lem1318252 : term8.
Proof. exact (conj (@lem1318250) (@lem1318251)). Qed.
Lemma lem1318253 : term9.
Proof. exact (conj (@lem1268295) (@lem1318252)). Qed.
Lemma lem1318254 : term10.
Proof. exact (conj (@lem1268060) (@lem1318253)). Qed.
Lemma lem1318255 : term11.
Proof. exact (conj (@lem1267990) (@lem1318254)). Qed.
Lemma lem1318257 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term12 Absty Repty mk R dest.
Proof. exact (fun h0 : term13 Absty Repty R dest mk => @lem38926 Absty Repty R dest mk h0). Qed.
Lemma lem1318258 (mk : type926) (R : type1554) (dest : type1546) : term14 mk R dest.
Proof. exact (@lem1318257 hreal nadd mk R dest). Qed.
Lemma lem1318259 : term15.
Proof. exact (@lem1318258 mk_hreal nadd_eq dest_hreal). Qed.
Lemma lem1318260 : term16.
Proof. exact (@lem1318259 (@lem1318255)). Qed.
Lemma lem1318261 : term17.
Proof. exact (proj2 (@lem1318260)). Qed.
Lemma lem1318262 : term18.
Proof. exact (proj2 (@lem1318261)). Qed.
Lemma lem1318267 : term19.
Proof. exact (proj1 (@lem1318262)). Qed.
Lemma lem1318268 (P : hreal -> Prop) : term20 P.
Proof. exact (@lem1318267 P). Qed.
Lemma lem1318269 (P : hreal -> Prop) : (term20 P) = ((term21 P) = (term22 P)).
Proof. exact (eq_refl (term20 P)). Qed.
Lemma lem1318271 : term23.
Proof. exact (proj1 (@lem1318261)). Qed.
Lemma lem1318272 (P : hreal -> Prop) : term24 P.
Proof. exact (@lem1318271 P). Qed.
Lemma lem1318273 (P : hreal -> Prop) : (term24 P) = ((term25 P) = (term26 P)).
Proof. exact (eq_refl (term24 P)). Qed.
Lemma lem1318306 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (P x) = (term2 Q x).
Proof. exact (EQ_MP (@lem1318245 P Q x) (@lem1318242 x P Q h1)). Qed.
Lemma lem1318307 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term27 P) = (term0 Q).
Proof. exact (fun_ext (fun x : nadd => @lem1318306 x P Q h1)). Qed.
Lemma lem1318308 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1318309 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term28 P) = (term21 Q).
Proof. exact (MK_COMB (@lem1318308) (@lem1318307 P Q h1)). Qed.
Lemma lem1318315 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318269 P) (@lem1318268 P)). Qed.
Lemma lem1318316 (Q : hreal -> Prop) : (term21 Q) = (term22 Q).
Proof. exact (@lem1318315 Q). Qed.
Lemma lem1318323 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term28 P) = (term22 Q).
Proof. exact (TRANS (@lem1318309 P Q h1) (@lem1318316 Q)). Qed.
Lemma lem1318324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1318325 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term29 P) = (term30 Q).
Proof. exact (MK_COMB (@lem1318324) (@lem1318323 P Q h1)). Qed.
Lemma lem1318367 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (P x) = (term2 Q x).
Proof. exact (EQ_MP (@lem1318245 P Q x) (@lem1318242 x P Q h1)). Qed.
Lemma lem1318368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1318369 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term31 P x) = (term32 Q x).
Proof. exact (MK_COMB (@lem1318368) (@lem1318367 x P Q h1)). Qed.
Lemma lem1318371 (x : nadd) (y : nadd) : (nadd_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1318372 (x : nadd) (M : nadd) : (nadd_le x M) = (term33 x M).
Proof. exact (@lem1318371 x M). Qed.
Lemma lem1318373 (x : nadd) (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term34 P x M) = (term35 Q x M).
Proof. exact (MK_COMB (@lem1318369 x P Q h1) (@lem1318372 x M)). Qed.
Lemma lem1318376 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term36 P M) = (term37 Q M).
Proof. exact (fun_ext (fun x : nadd => @lem1318373 x M P Q h1)). Qed.
Lemma lem1318377 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318378 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M) = (term39 Q M).
Proof. exact (MK_COMB (@lem1318377) (@lem1318376 M P Q h1)). Qed.
Lemma lem1318384 (P : hreal -> Prop) : (term25 P) = (term26 P).
Proof. exact (EQ_MP (@lem1318273 P) (@lem1318272 P)). Qed.
Lemma lem1318385 (Q : hreal -> Prop) (M : nadd) : (term40 Q M) = (term41 Q M).
Proof. exact (@lem1318384 (term42 Q M)). Qed.
Lemma lem1318386 (Q : hreal -> Prop) (x : nadd) (M : nadd) : (term43 Q M x) = (term35 Q x M).
Proof. exact (eq_refl (term43 Q M x)). Qed.
Lemma lem1318387 (Q : hreal -> Prop) (M : nadd) : (term44 Q M) = (term37 Q M).
Proof. exact (fun_ext (fun x : nadd => @lem1318386 Q x M)). Qed.
Lemma lem1318388 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318389 (Q : hreal -> Prop) (M : nadd) : (term40 Q M) = (term39 Q M).
Proof. exact (MK_COMB (@lem1318388) (@lem1318387 Q M)). Qed.
Lemma lem1318390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318391 (Q : hreal -> Prop) (M : nadd) : (term45 Q M) = (term46 Q M).
Proof. exact (MK_COMB (@lem1318390) (@lem1318389 Q M)). Qed.
Lemma lem1318392 (Q : hreal -> Prop) (x : hreal) (M : nadd) : (term47 Q M x) = (term48 Q x M).
Proof. exact (eq_refl (term47 Q M x)). Qed.
Lemma lem1318393 (Q : hreal -> Prop) (M : nadd) : (term49 Q M) = (term42 Q M).
Proof. exact (fun_ext (fun x : hreal => @lem1318392 Q x M)). Qed.
Lemma lem1318394 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1318395 (Q : hreal -> Prop) (M : nadd) : (term41 Q M) = (term50 Q M).
Proof. exact (MK_COMB (@lem1318394) (@lem1318393 Q M)). Qed.
Lemma lem1318396 (Q : hreal -> Prop) (M : nadd) : ((term40 Q M) = (term41 Q M)) = ((term39 Q M) = (term50 Q M)).
Proof. exact (MK_COMB (@lem1318391 Q M) (@lem1318395 Q M)). Qed.
Lemma lem1318397 (Q : hreal -> Prop) (M : nadd) : (term39 Q M) = (term50 Q M).
Proof. exact (EQ_MP (@lem1318396 Q M) (@lem1318385 Q M)). Qed.
Lemma lem1318406 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M) = (term50 Q M).
Proof. exact (TRANS (@lem1318378 M P Q h1) (@lem1318397 Q M)). Qed.
Lemma lem1318407 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term51 P) = (term52 Q).
Proof. exact (fun_ext (fun M : nadd => @lem1318406 M P Q h1)). Qed.
Lemma lem1318408 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1318409 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term53 P) = (term54 Q).
Proof. exact (MK_COMB (@lem1318408) (@lem1318407 P Q h1)). Qed.
Lemma lem1318415 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318269 P) (@lem1318268 P)). Qed.
Lemma lem1318416 (Q : hreal -> Prop) : (term55 Q) = (term56 Q).
Proof. exact (@lem1318415 (term57 Q)). Qed.
Lemma lem1318417 (Q : hreal -> Prop) (M : nadd) : (term58 Q M) = (term50 Q M).
Proof. exact (eq_refl (term58 Q M)). Qed.
Lemma lem1318418 (Q : hreal -> Prop) : (term59 Q) = (term52 Q).
Proof. exact (fun_ext (fun M : nadd => @lem1318417 Q M)). Qed.
Lemma lem1318419 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1318420 (Q : hreal -> Prop) : (term55 Q) = (term54 Q).
Proof. exact (MK_COMB (@lem1318419) (@lem1318418 Q)). Qed.
Lemma lem1318421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318422 (Q : hreal -> Prop) : (term60 Q) = (term61 Q).
Proof. exact (MK_COMB (@lem1318421) (@lem1318420 Q)). Qed.
Lemma lem1318423 (Q : hreal -> Prop) (M : hreal) : (term62 Q M) = (term63 Q M).
Proof. exact (eq_refl (term62 Q M)). Qed.
Lemma lem1318424 (Q : hreal -> Prop) : (term64 Q) = (term57 Q).
Proof. exact (fun_ext (fun M : hreal => @lem1318423 Q M)). Qed.
Lemma lem1318425 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1318426 (Q : hreal -> Prop) : (term56 Q) = (term65 Q).
Proof. exact (MK_COMB (@lem1318425) (@lem1318424 Q)). Qed.
Lemma lem1318427 (Q : hreal -> Prop) : ((term55 Q) = (term56 Q)) = ((term54 Q) = (term65 Q)).
Proof. exact (MK_COMB (@lem1318422 Q) (@lem1318426 Q)). Qed.
Lemma lem1318428 (Q : hreal -> Prop) : (term54 Q) = (term65 Q).
Proof. exact (EQ_MP (@lem1318427 Q) (@lem1318416 Q)). Qed.
Lemma lem1318443 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term53 P) = (term65 Q).
Proof. exact (TRANS (@lem1318409 P Q h1) (@lem1318428 Q)). Qed.
Lemma lem1318444 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term66 P) = (term67 Q).
Proof. exact (MK_COMB (@lem1318325 P Q h1) (@lem1318443 P Q h1)). Qed.
Lemma lem1318447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1318448 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term68 P) = (term69 Q).
Proof. exact (MK_COMB (@lem1318447) (@lem1318444 P Q h1)). Qed.
Lemma lem1318492 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (P x) = (term2 Q x).
Proof. exact (EQ_MP (@lem1318245 P Q x) (@lem1318242 x P Q h1)). Qed.
Lemma lem1318493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1318494 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term31 P x) = (term32 Q x).
Proof. exact (MK_COMB (@lem1318493) (@lem1318492 x P Q h1)). Qed.
Lemma lem1318496 (x : nadd) (y : nadd) : (nadd_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1318497 (x : nadd) (M : nadd) : (nadd_le x M) = (term33 x M).
Proof. exact (@lem1318496 x M). Qed.
Lemma lem1318498 (x : nadd) (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term34 P x M) = (term35 Q x M).
Proof. exact (MK_COMB (@lem1318494 x P Q h1) (@lem1318497 x M)). Qed.
Lemma lem1318501 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term36 P M) = (term37 Q M).
Proof. exact (fun_ext (fun x : nadd => @lem1318498 x M P Q h1)). Qed.
Lemma lem1318502 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318503 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M) = (term39 Q M).
Proof. exact (MK_COMB (@lem1318502) (@lem1318501 M P Q h1)). Qed.
Lemma lem1318509 (P : hreal -> Prop) : (term25 P) = (term26 P).
Proof. exact (EQ_MP (@lem1318273 P) (@lem1318272 P)). Qed.
Lemma lem1318510 (Q : hreal -> Prop) (M : nadd) : (term40 Q M) = (term41 Q M).
Proof. exact (@lem1318509 (term42 Q M)). Qed.
Lemma lem1318511 (Q : hreal -> Prop) (x : nadd) (M : nadd) : (term43 Q M x) = (term35 Q x M).
Proof. exact (eq_refl (term43 Q M x)). Qed.
Lemma lem1318512 (Q : hreal -> Prop) (M : nadd) : (term44 Q M) = (term37 Q M).
Proof. exact (fun_ext (fun x : nadd => @lem1318511 Q x M)). Qed.
Lemma lem1318513 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318514 (Q : hreal -> Prop) (M : nadd) : (term40 Q M) = (term39 Q M).
Proof. exact (MK_COMB (@lem1318513) (@lem1318512 Q M)). Qed.
Lemma lem1318515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318516 (Q : hreal -> Prop) (M : nadd) : (term45 Q M) = (term46 Q M).
Proof. exact (MK_COMB (@lem1318515) (@lem1318514 Q M)). Qed.
Lemma lem1318517 (Q : hreal -> Prop) (x : hreal) (M : nadd) : (term47 Q M x) = (term48 Q x M).
Proof. exact (eq_refl (term47 Q M x)). Qed.
Lemma lem1318518 (Q : hreal -> Prop) (M : nadd) : (term49 Q M) = (term42 Q M).
Proof. exact (fun_ext (fun x : hreal => @lem1318517 Q x M)). Qed.
Lemma lem1318519 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1318520 (Q : hreal -> Prop) (M : nadd) : (term41 Q M) = (term50 Q M).
Proof. exact (MK_COMB (@lem1318519) (@lem1318518 Q M)). Qed.
Lemma lem1318521 (Q : hreal -> Prop) (M : nadd) : ((term40 Q M) = (term41 Q M)) = ((term39 Q M) = (term50 Q M)).
Proof. exact (MK_COMB (@lem1318516 Q M) (@lem1318520 Q M)). Qed.
Lemma lem1318522 (Q : hreal -> Prop) (M : nadd) : (term39 Q M) = (term50 Q M).
Proof. exact (EQ_MP (@lem1318521 Q M) (@lem1318510 Q M)). Qed.
Lemma lem1318531 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M) = (term50 Q M).
Proof. exact (TRANS (@lem1318503 M P Q h1) (@lem1318522 Q M)). Qed.
Lemma lem1318532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1318533 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term70 P M) = (term71 Q M).
Proof. exact (MK_COMB (@lem1318532) (@lem1318531 M P Q h1)). Qed.
Lemma lem1318577 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (P x) = (term2 Q x).
Proof. exact (EQ_MP (@lem1318245 P Q x) (@lem1318242 x P Q h1)). Qed.
Lemma lem1318578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1318579 (x : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term31 P x) = (term32 Q x).
Proof. exact (MK_COMB (@lem1318578) (@lem1318577 x P Q h1)). Qed.
Lemma lem1318581 (x : nadd) (y : nadd) : (nadd_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1318582 (x : nadd) (M' : nadd) : (nadd_le x M') = (term33 x M').
Proof. exact (@lem1318581 x M'). Qed.
Lemma lem1318583 (x : nadd) (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term34 P x M') = (term35 Q x M').
Proof. exact (MK_COMB (@lem1318579 x P Q h1) (@lem1318582 x M')). Qed.
Lemma lem1318586 (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term36 P M') = (term37 Q M').
Proof. exact (fun_ext (fun x : nadd => @lem1318583 x M' P Q h1)). Qed.
Lemma lem1318587 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318588 (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M') = (term39 Q M').
Proof. exact (MK_COMB (@lem1318587) (@lem1318586 M' P Q h1)). Qed.
Lemma lem1318594 (P : hreal -> Prop) : (term25 P) = (term26 P).
Proof. exact (EQ_MP (@lem1318273 P) (@lem1318272 P)). Qed.
Lemma lem1318595 (Q : hreal -> Prop) (M' : nadd) : (term40 Q M') = (term41 Q M').
Proof. exact (@lem1318594 (term42 Q M')). Qed.
Lemma lem1318596 (Q : hreal -> Prop) (x : nadd) (M' : nadd) : (term43 Q M' x) = (term35 Q x M').
Proof. exact (eq_refl (term43 Q M' x)). Qed.
Lemma lem1318597 (Q : hreal -> Prop) (M' : nadd) : (term44 Q M') = (term37 Q M').
Proof. exact (fun_ext (fun x : nadd => @lem1318596 Q x M')). Qed.
Lemma lem1318598 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318599 (Q : hreal -> Prop) (M' : nadd) : (term40 Q M') = (term39 Q M').
Proof. exact (MK_COMB (@lem1318598) (@lem1318597 Q M')). Qed.
Lemma lem1318600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318601 (Q : hreal -> Prop) (M' : nadd) : (term45 Q M') = (term46 Q M').
Proof. exact (MK_COMB (@lem1318600) (@lem1318599 Q M')). Qed.
Lemma lem1318602 (Q : hreal -> Prop) (x : hreal) (M' : nadd) : (term47 Q M' x) = (term48 Q x M').
Proof. exact (eq_refl (term47 Q M' x)). Qed.
Lemma lem1318603 (Q : hreal -> Prop) (M' : nadd) : (term49 Q M') = (term42 Q M').
Proof. exact (fun_ext (fun x : hreal => @lem1318602 Q x M')). Qed.
Lemma lem1318604 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1318605 (Q : hreal -> Prop) (M' : nadd) : (term41 Q M') = (term50 Q M').
Proof. exact (MK_COMB (@lem1318604) (@lem1318603 Q M')). Qed.
Lemma lem1318606 (Q : hreal -> Prop) (M' : nadd) : ((term40 Q M') = (term41 Q M')) = ((term39 Q M') = (term50 Q M')).
Proof. exact (MK_COMB (@lem1318601 Q M') (@lem1318605 Q M')). Qed.
Lemma lem1318607 (Q : hreal -> Prop) (M' : nadd) : (term39 Q M') = (term50 Q M').
Proof. exact (EQ_MP (@lem1318606 Q M') (@lem1318595 Q M')). Qed.
Lemma lem1318616 (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term38 P M') = (term50 Q M').
Proof. exact (TRANS (@lem1318588 M' P Q h1) (@lem1318607 Q M')). Qed.
Lemma lem1318617 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1318618 (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term72 P M') = (term73 Q M').
Proof. exact (MK_COMB (@lem1318617) (@lem1318616 M' P Q h1)). Qed.
Lemma lem1318620 (x : nadd) (y : nadd) : (nadd_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1318621 (M : nadd) (M' : nadd) : (nadd_le M M') = (term33 M M').
Proof. exact (@lem1318620 M M'). Qed.
Lemma lem1318622 (M : nadd) (M' : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term74 P M M') = (term75 Q M M').
Proof. exact (MK_COMB (@lem1318618 M' P Q h1) (@lem1318621 M M')). Qed.
Lemma lem1318625 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term76 P M) = (term77 Q M).
Proof. exact (fun_ext (fun M' : nadd => @lem1318622 M M' P Q h1)). Qed.
Lemma lem1318626 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318627 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term78 P M) = (term79 Q M).
Proof. exact (MK_COMB (@lem1318626) (@lem1318625 M P Q h1)). Qed.
Lemma lem1318633 (P : hreal -> Prop) : (term25 P) = (term26 P).
Proof. exact (EQ_MP (@lem1318273 P) (@lem1318272 P)). Qed.
Lemma lem1318634 (Q : hreal -> Prop) (M : nadd) : (term80 Q M) = (term81 Q M).
Proof. exact (@lem1318633 (term82 Q M)). Qed.
Lemma lem1318635 (Q : hreal -> Prop) (M : nadd) (M' : nadd) : (term83 Q M M') = (term75 Q M M').
Proof. exact (eq_refl (term83 Q M M')). Qed.
Lemma lem1318636 (Q : hreal -> Prop) (M : nadd) : (term84 Q M) = (term77 Q M).
Proof. exact (fun_ext (fun M' : nadd => @lem1318635 Q M M')). Qed.
Lemma lem1318637 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1318638 (Q : hreal -> Prop) (M : nadd) : (term80 Q M) = (term79 Q M).
Proof. exact (MK_COMB (@lem1318637) (@lem1318636 Q M)). Qed.
Lemma lem1318639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318640 (Q : hreal -> Prop) (M : nadd) : (term85 Q M) = (term86 Q M).
Proof. exact (MK_COMB (@lem1318639) (@lem1318638 Q M)). Qed.
Lemma lem1318641 (Q : hreal -> Prop) (M : nadd) (M' : hreal) : (term87 Q M M') = (term88 Q M M').
Proof. exact (eq_refl (term87 Q M M')). Qed.
Lemma lem1318642 (Q : hreal -> Prop) (M : nadd) : (term89 Q M) = (term82 Q M).
Proof. exact (fun_ext (fun M' : hreal => @lem1318641 Q M M')). Qed.
Lemma lem1318643 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1318644 (Q : hreal -> Prop) (M : nadd) : (term81 Q M) = (term90 Q M).
Proof. exact (MK_COMB (@lem1318643) (@lem1318642 Q M)). Qed.
Lemma lem1318645 (Q : hreal -> Prop) (M : nadd) : ((term80 Q M) = (term81 Q M)) = ((term79 Q M) = (term90 Q M)).
Proof. exact (MK_COMB (@lem1318640 Q M) (@lem1318644 Q M)). Qed.
Lemma lem1318646 (Q : hreal -> Prop) (M : nadd) : (term79 Q M) = (term90 Q M).
Proof. exact (EQ_MP (@lem1318645 Q M) (@lem1318634 Q M)). Qed.
Lemma lem1318663 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term78 P M) = (term90 Q M).
Proof. exact (TRANS (@lem1318627 M P Q h1) (@lem1318646 Q M)). Qed.
Lemma lem1318664 (M : nadd) (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term91 P M) = (term92 Q M).
Proof. exact (MK_COMB (@lem1318533 M P Q h1) (@lem1318663 M P Q h1)). Qed.
Lemma lem1318667 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term93 P) = (term94 Q).
Proof. exact (fun_ext (fun M : nadd => @lem1318664 M P Q h1)). Qed.
Lemma lem1318668 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1318669 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term95 P) = (term96 Q).
Proof. exact (MK_COMB (@lem1318668) (@lem1318667 P Q h1)). Qed.
Lemma lem1318675 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318269 P) (@lem1318268 P)). Qed.
Lemma lem1318676 (Q : hreal -> Prop) : (term97 Q) = (term98 Q).
Proof. exact (@lem1318675 (term99 Q)). Qed.
Lemma lem1318677 (Q : hreal -> Prop) (M : nadd) : (term100 Q M) = (term92 Q M).
Proof. exact (eq_refl (term100 Q M)). Qed.
Lemma lem1318678 (Q : hreal -> Prop) : (term101 Q) = (term94 Q).
Proof. exact (fun_ext (fun M : nadd => @lem1318677 Q M)). Qed.
Lemma lem1318679 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1318680 (Q : hreal -> Prop) : (term97 Q) = (term96 Q).
Proof. exact (MK_COMB (@lem1318679) (@lem1318678 Q)). Qed.
Lemma lem1318681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318682 (Q : hreal -> Prop) : (term102 Q) = (term103 Q).
Proof. exact (MK_COMB (@lem1318681) (@lem1318680 Q)). Qed.
Lemma lem1318683 (Q : hreal -> Prop) (M : hreal) : (term104 Q M) = (term105 Q M).
Proof. exact (eq_refl (term104 Q M)). Qed.
Lemma lem1318684 (Q : hreal -> Prop) : (term106 Q) = (term99 Q).
Proof. exact (fun_ext (fun M : hreal => @lem1318683 Q M)). Qed.
Lemma lem1318685 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1318686 (Q : hreal -> Prop) : (term98 Q) = (term107 Q).
Proof. exact (MK_COMB (@lem1318685) (@lem1318684 Q)). Qed.
Lemma lem1318687 (Q : hreal -> Prop) : ((term97 Q) = (term98 Q)) = ((term96 Q) = (term107 Q)).
Proof. exact (MK_COMB (@lem1318682 Q) (@lem1318686 Q)). Qed.
Lemma lem1318688 (Q : hreal -> Prop) : (term96 Q) = (term107 Q).
Proof. exact (EQ_MP (@lem1318687 Q) (@lem1318676 Q)). Qed.
Lemma lem1318721 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term95 P) = (term107 Q).
Proof. exact (TRANS (@lem1318669 P Q h1) (@lem1318688 Q)). Qed.
Lemma lem1318722 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : (term5 P) = (term108 Q).
Proof. exact (MK_COMB (@lem1318448 P Q h1) (@lem1318721 P Q h1)). Qed.
Lemma lem1318725 (P : nadd -> Prop) (Q : hreal -> Prop) (h1 : P = (term0 Q)) : term108 Q.
Proof. exact (EQ_MP (@lem1318722 P Q h1) (@lem1318249 P)). Qed.
Lemma lem1318726 (Q : hreal -> Prop) : (term0 Q) = (term0 Q).
Proof. exact (eq_refl (term0 Q)). Qed.
Lemma lem1318729 (P : nadd -> Prop) (Q : hreal -> Prop) : term109 P Q.
Proof. exact (fun h0 : P = (term0 Q) => @lem1318725 P Q h0). Qed.
Lemma lem1318730 (Q : hreal -> Prop) : term110 Q.
Proof. exact (@lem1318729 (term0 Q) Q). Qed.
Lemma lem1318731 (Q : hreal -> Prop) : term108 Q.
Proof. exact (@lem1318730 Q (@lem1318726 Q)). Qed.
Lemma lem1318736 : term111.
Proof. exact (fun Q : hreal -> Prop => @lem1318731 Q). Qed.
