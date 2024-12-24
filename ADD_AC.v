Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_AC_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem77972 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem77973 (n : nat) (m : nat) (p : nat) : (term1 n m p) = (term2 n m p).
Proof. exact (@lem77972 (term1 n m p)). Qed.
Lemma lem77974 (n : nat) (m : nat) (p : nat) : (term2 n m p) = (term1 n m p).
Proof. exact (SYM (@lem77973 n m p)). Qed.
Lemma lem77975 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem77978 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem77979 (n : nat) (m : nat) (p : nat) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem77978 n m p h0). Qed.
Lemma lem77980 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem77981 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem77982 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem77980 n m p h2 (@lem77981 n m p h1)). Qed.
Lemma lem77983 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term6 n m p.
Proof. exact (fun h0 : term5 n m p => @lem77982 n m p h1 h0). Qed.
Lemma lem77984 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem77985 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem77983 n m p h1 (@lem77984 n m p h2)). Qed.
Lemma lem77986 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem77985 n m p h0 h1). Qed.
Lemma lem77987 (n : nat) (m : nat) (p : nat) : term7 n m p.
Proof. exact (fun h0 : term5 n m p => @lem77986 n m p h0). Qed.
Lemma lem77990 (n : nat) (m : nat) (p : nat) : term5 n m p.
Proof. exact (@lem77987 n m p (@lem77979 n m p)). Qed.
Lemma lem78020 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem78021 : term8 = term9.
Proof. exact (@lem78020 term10). Qed.
Lemma lem78034 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem78035 : term12 = term13.
Proof. exact (MK_COMB (@lem78034) (@lem78021)). Qed.
Lemma lem78038 (n : nat) (m : nat) (p : nat) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem78039 (n : nat) (m : nat) (p : nat) : (term4 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem78038 n m p) (@lem78035)). Qed.
Lemma lem78042 (m : nat) (p : nat) : (term16 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : nat => @lem78039 n m p)). Qed.
Lemma lem78043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78044 (m : nat) (p : nat) : (term18 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem78043) (@lem78042 m p)). Qed.
Lemma lem78049 (p : nat) : (term20 p) = (term21 p).
Proof. exact (fun_ext (fun m : nat => @lem78044 m p)). Qed.
Lemma lem78050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78051 (p : nat) : (term22 p) = (term23 p).
Proof. exact (MK_COMB (@lem78050) (@lem78049 p)). Qed.
Lemma lem78056 : term24 = term25.
Proof. exact (fun_ext (fun p : nat => @lem78051 p)). Qed.
Lemma lem78057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78066 : term26 = term27.
Proof. exact (MK_COMB (@lem78057) (@lem78056)). Qed.
Lemma lem78067 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78068 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem78067 m n p)). Qed.
Lemma lem78069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78070 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem78069) (@lem78068 m n)). Qed.
Lemma lem78071 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem78070 m n)). Qed.
Lemma lem78072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78073 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem78072) (@lem78071 m)). Qed.
Lemma lem78074 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem78073 m)). Qed.
Lemma lem78075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78076 : term10 = term10.
Proof. exact (MK_COMB (@lem78075) (@lem78074)). Qed.
Lemma lem78077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem78078 : term9 = term9.
Proof. exact (MK_COMB (@lem78077) (@lem78076)). Qed.
Lemma lem78079 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78080 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem78079 n m)). Qed.
Lemma lem78081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78082 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem78081) (@lem78080 m)). Qed.
Lemma lem78083 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem78082 m)). Qed.
Lemma lem78084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78085 : term38 = term38.
Proof. exact (MK_COMB (@lem78084) (@lem78083)). Qed.
Lemma lem78086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem78087 : term11 = term11.
Proof. exact (MK_COMB (@lem78086) (@lem78085)). Qed.
Lemma lem78088 : term13 = term13.
Proof. exact (MK_COMB (@lem78087) (@lem78078)). Qed.
Lemma lem78101 (n : nat) (m : nat) (p : nat) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem78102 (n : nat) (m : nat) (p : nat) : (term15 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem78101 n m p) (@lem78088)). Qed.
Lemma lem78103 (m : nat) (p : nat) : (term17 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : nat => @lem78102 n m p)). Qed.
Lemma lem78104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78105 (m : nat) (p : nat) : (term19 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem78104) (@lem78103 m p)). Qed.
Lemma lem78106 (p : nat) : (term21 p) = (term21 p).
Proof. exact (fun_ext (fun m : nat => @lem78105 m p)). Qed.
Lemma lem78107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78108 (p : nat) : (term23 p) = (term23 p).
Proof. exact (MK_COMB (@lem78107) (@lem78106 p)). Qed.
Lemma lem78109 : term25 = term25.
Proof. exact (fun_ext (fun p : nat => @lem78108 p)). Qed.
Lemma lem78110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78111 : term27 = term27.
Proof. exact (MK_COMB (@lem78110) (@lem78109)). Qed.
Lemma lem78170 : term26 = term27.
Proof. exact (TRANS (@lem78066) (@lem78111)). Qed.
Lemma lem78171 : term27 = term26.
Proof. exact (SYM (@lem78170)). Qed.
Lemma lem78172 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem78173 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem78174 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem78182 (n : nat) (m : nat) (p : nat) : (term39 n m p) = (term40 n m p).
Proof. exact (@lem17045 ((term29 m n p) = (term28 m n p)) ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem78184 (n : nat) (m : nat) : (term41 n m) = (term41 n m).
Proof. exact (eq_refl (term41 n m)). Qed.
Lemma lem78185 (n : nat) (m : nat) (p : nat) : (term42 n m p) = (term43 n m p).
Proof. exact (MK_COMB (@lem78184 n m) (@lem78182 n m p)). Qed.
Lemma lem78186 (n : nat) (m : nat) (p : nat) : (term3 n m p) = (term42 n m p).
Proof. exact (@lem17045 ((Nat.add m n) = (Nat.add n m)) (term44 n m p)). Qed.
Lemma lem78191 (n : nat) (m : nat) (p : nat) : (term3 n m p) = (term43 n m p).
Proof. exact (TRANS (@lem78186 n m p) (@lem78185 n m p)). Qed.
Lemma lem78193 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78194 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem78193 n m)). Qed.
Lemma lem78195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78196 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem78195) (@lem78194 m)). Qed.
Lemma lem78197 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem78196 m)). Qed.
Lemma lem78198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78211 : term38 = term38.
Proof. exact (MK_COMB (@lem78198) (@lem78197)). Qed.
Lemma lem78212 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem78211) (@lem78173 h1)). Qed.
Lemma lem78213 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78214 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem78213 m n p)). Qed.
Lemma lem78215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78216 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem78215) (@lem78214 m n)). Qed.
Lemma lem78217 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem78216 m n)). Qed.
Lemma lem78218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78219 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem78218) (@lem78217 m)). Qed.
Lemma lem78220 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem78219 m)). Qed.
Lemma lem78221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78238 : term10 = term10.
Proof. exact (MK_COMB (@lem78221) (@lem78220)). Qed.
Lemma lem78239 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem78238) (@lem78174 h1)). Qed.
Lemma lem78307 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term43 n m p.
Proof. exact (EQ_MP (@lem78191 n m p) (@lem78172 n m p h1)). Qed.
Lemma lem78320 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78321 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem78320 n m)). Qed.
Lemma lem78322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78323 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem78322) (@lem78321 m)). Qed.
Lemma lem78324 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem78323 m)). Qed.
Lemma lem78325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78326 : term38 = term38.
Proof. exact (MK_COMB (@lem78325) (@lem78324)). Qed.
Lemma lem78327 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem78326) (@lem78212 h1)). Qed.
Lemma lem78348 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78349 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem78348 m n p)). Qed.
Lemma lem78350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78351 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem78350) (@lem78349 m n)). Qed.
Lemma lem78352 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem78351 m n)). Qed.
Lemma lem78353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78354 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem78353) (@lem78352 m)). Qed.
Lemma lem78355 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem78354 m)). Qed.
Lemma lem78356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78357 : term10 = term10.
Proof. exact (MK_COMB (@lem78356) (@lem78355)). Qed.
Lemma lem78358 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem78357) (@lem78239 h1)). Qed.
Lemma lem78360 (n : nat) (m : nat) (p : nat) (h1 : term40 n m p) : term40 n m p.
Proof. exact (h1). Qed.
Lemma lem78364 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78365 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem78364 n m)). Qed.
Lemma lem78366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78367 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem78366) (@lem78365 m)). Qed.
Lemma lem78368 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem78367 m)). Qed.
Lemma lem78369 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78371 : term38 = term38.
Proof. exact (MK_COMB (@lem78369) (@lem78368)). Qed.
Lemma lem78372 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem78371) (@lem78327 h1)). Qed.
Lemma lem78389 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem78401 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78402 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem78401 m n p)). Qed.
Lemma lem78403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78404 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem78403) (@lem78402 m n)). Qed.
Lemma lem78405 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem78404 m n)). Qed.
Lemma lem78406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78407 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem78406) (@lem78405 m)). Qed.
Lemma lem78408 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem78407 m)). Qed.
Lemma lem78409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78411 : term10 = term10.
Proof. exact (MK_COMB (@lem78409) (@lem78408)). Qed.
Lemma lem78412 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem78411) (@lem78358 h1)). Qed.
Lemma lem78416 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem78418 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78419 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem78418 n m)). Qed.
Lemma lem78420 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78421 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem78420) (@lem78419 m)). Qed.
Lemma lem78422 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem78421 m)). Qed.
Lemma lem78423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78425 : term38 = term38.
Proof. exact (MK_COMB (@lem78423) (@lem78422)). Qed.
Lemma lem78426 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem78425) (@lem78327 h1)). Qed.
Lemma lem78428 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78429 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem78428 m n p)). Qed.
Lemma lem78430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78431 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem78430) (@lem78429 m n)). Qed.
Lemma lem78432 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem78431 m n)). Qed.
Lemma lem78433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78434 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem78433) (@lem78432 m)). Qed.
Lemma lem78435 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem78434 m)). Qed.
Lemma lem78436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem78438 : term10 = term10.
Proof. exact (MK_COMB (@lem78436) (@lem78435)). Qed.
Lemma lem78439 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem78438) (@lem78358 h1)). Qed.
Lemma lem78443 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem78444 (_2156 : nat) (h1 : term38) : term48 _2156.
Proof. exact (@lem78372 h1 _2156). Qed.
Lemma lem78445 (_2156 : nat) : (term48 _2156) = (term36 _2156).
Proof. exact (eq_refl (term48 _2156)). Qed.
Lemma lem78446 (_2156 : nat) (h1 : term38) : term36 _2156.
Proof. exact (EQ_MP (@lem78445 _2156) (@lem78444 _2156 h1)). Qed.
Lemma lem78447 (_2156 : nat) (_2157 : nat) (h1 : term38) : term49 _2156 _2157.
Proof. exact (@lem78446 _2156 h1 _2157). Qed.
Lemma lem78448 (_2157 : nat) (_2156 : nat) : (term49 _2156 _2157) = ((Nat.add _2156 _2157) = (Nat.add _2157 _2156)).
Proof. exact (eq_refl (term49 _2156 _2157)). Qed.
Lemma lem78465 (_2163 : nat) (h1 : term10) : term50 _2163.
Proof. exact (@lem78412 h1 _2163). Qed.
Lemma lem78466 (_2163 : nat) : (term50 _2163) = (term33 _2163).
Proof. exact (eq_refl (term50 _2163)). Qed.
Lemma lem78467 (_2163 : nat) (h1 : term10) : term33 _2163.
Proof. exact (EQ_MP (@lem78466 _2163) (@lem78465 _2163 h1)). Qed.
Lemma lem78468 (_2163 : nat) (_2164 : nat) (h1 : term10) : term51 _2163 _2164.
Proof. exact (@lem78467 _2163 h1 _2164). Qed.
Lemma lem78469 (_2163 : nat) (_2164 : nat) : (term51 _2163 _2164) = (term31 _2163 _2164).
Proof. exact (eq_refl (term51 _2163 _2164)). Qed.
Lemma lem78470 (_2163 : nat) (_2164 : nat) (h1 : term10) : term31 _2163 _2164.
Proof. exact (EQ_MP (@lem78469 _2163 _2164) (@lem78468 _2163 _2164 h1)). Qed.
Lemma lem78471 (_2163 : nat) (_2164 : nat) (_2165 : nat) (h1 : term10) : term52 _2163 _2164 _2165.
Proof. exact (@lem78470 _2163 _2164 h1 _2165). Qed.
Lemma lem78472 (_2163 : nat) (_2164 : nat) (_2165 : nat) : (term52 _2163 _2164 _2165) = ((term28 _2163 _2164 _2165) = (term29 _2163 _2164 _2165)).
Proof. exact (eq_refl (term52 _2163 _2164 _2165)). Qed.
Lemma lem78474 (_2166 : nat) (h1 : term38) : term48 _2166.
Proof. exact (@lem78426 h1 _2166). Qed.
Lemma lem78475 (_2166 : nat) : (term48 _2166) = (term36 _2166).
Proof. exact (eq_refl (term48 _2166)). Qed.
Lemma lem78476 (_2166 : nat) (h1 : term38) : term36 _2166.
Proof. exact (EQ_MP (@lem78475 _2166) (@lem78474 _2166 h1)). Qed.
Lemma lem78477 (_2166 : nat) (_2167 : nat) (h1 : term38) : term49 _2166 _2167.
Proof. exact (@lem78476 _2166 h1 _2167). Qed.
Lemma lem78478 (_2167 : nat) (_2166 : nat) : (term49 _2166 _2167) = ((Nat.add _2166 _2167) = (Nat.add _2167 _2166)).
Proof. exact (eq_refl (term49 _2166 _2167)). Qed.
Lemma lem78480 (_2168 : nat) (h1 : term10) : term50 _2168.
Proof. exact (@lem78439 h1 _2168). Qed.
Lemma lem78481 (_2168 : nat) : (term50 _2168) = (term33 _2168).
Proof. exact (eq_refl (term50 _2168)). Qed.
Lemma lem78482 (_2168 : nat) (h1 : term10) : term33 _2168.
Proof. exact (EQ_MP (@lem78481 _2168) (@lem78480 _2168 h1)). Qed.
Lemma lem78483 (_2168 : nat) (_2169 : nat) (h1 : term10) : term51 _2168 _2169.
Proof. exact (@lem78482 _2168 h1 _2169). Qed.
Lemma lem78484 (_2168 : nat) (_2169 : nat) : (term51 _2168 _2169) = (term31 _2168 _2169).
Proof. exact (eq_refl (term51 _2168 _2169)). Qed.
Lemma lem78485 (_2168 : nat) (_2169 : nat) (h1 : term10) : term31 _2168 _2169.
Proof. exact (EQ_MP (@lem78484 _2168 _2169) (@lem78483 _2168 _2169 h1)). Qed.
Lemma lem78486 (_2168 : nat) (_2169 : nat) (_2170 : nat) (h1 : term10) : term52 _2168 _2169 _2170.
Proof. exact (@lem78485 _2168 _2169 h1 _2170). Qed.
Lemma lem78487 (_2168 : nat) (_2169 : nat) (_2170 : nat) : (term52 _2168 _2169 _2170) = ((term28 _2168 _2169 _2170) = (term29 _2168 _2169 _2170)).
Proof. exact (eq_refl (term52 _2168 _2169 _2170)). Qed.
Lemma lem78494 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem78500 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem78506 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem78525 (_2157 : nat) (_2156 : nat) (h1 : term38) : (Nat.add _2156 _2157) = (Nat.add _2157 _2156).
Proof. exact (EQ_MP (@lem78448 _2157 _2156) (@lem78447 _2156 _2157 h1)). Qed.
Lemma lem78526 (n : nat) (m : nat) (h1 : term38) : (Nat.add m n) = (Nat.add n m).
Proof. exact (@lem78525 n m h1). Qed.
Lemma lem78527 (n : nat) (m : nat) (h1 : term38) : term53 n m.
Proof. exact (fun h0 : term45 n m => @lem78526 n m h1). Qed.
Lemma lem78529 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78530 (n : nat) (m : nat) : (term53 n m) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (@lem78529 ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78531 (n : nat) (m : nat) (h1 : term38) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem78530 n m) (@lem78527 n m h1)). Qed.
Lemma lem78534 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem78536 (n : nat) (m : nat) : (term45 n m) = (term55 n m).
Proof. exact (@lem78534 ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem78539 (n : nat) (m : nat) (h1 : term45 n m) : term55 n m.
Proof. exact (EQ_MP (@lem78536 n m) (@lem78494 n m h1)). Qed.
Lemma lem78542 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (@lem78539 n m h2 (@lem78531 n m h1)). Qed.
Lemma lem78543 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : term56.
Proof. exact (fun h0 : ~ False => @lem78542 n m h1 h2). Qed.
Lemma lem78545 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78546 : term56 = False.
Proof. exact (@lem78545 False). Qed.
Lemma lem78547 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem78546) (@lem78543 n m h1 h2)). Qed.
Lemma lem78564 (x : nat) (y : nat) (z : nat) : term57 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem78566 (_2163 : nat) (_2164 : nat) (_2165 : nat) (h1 : term10) : (term28 _2163 _2164 _2165) = (term29 _2163 _2164 _2165).
Proof. exact (EQ_MP (@lem78472 _2163 _2164 _2165) (@lem78471 _2163 _2164 _2165 h1)). Qed.
Lemma lem78567 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (@lem78566 m n p h1). Qed.
Lemma lem78568 (m : nat) (n : nat) (p : nat) (h1 : term10) : term58 m n p.
Proof. exact (fun h0 : term59 m n p => @lem78567 m n p h1). Qed.
Lemma lem78570 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78571 (m : nat) (n : nat) (p : nat) : (term58 m n p) = ((term28 m n p) = (term29 m n p)).
Proof. exact (@lem78570 ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem78572 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (EQ_MP (@lem78571 m n p) (@lem78568 m n p h1)). Qed.
Lemma lem78574 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem78575 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term28 m n p).
Proof. exact (@lem78574 (term28 m n p)). Qed.
Lemma lem78576 (m : nat) (n : nat) (p : nat) : term60 m n p.
Proof. exact (fun h0 : term61 m n p => @lem78575 m n p). Qed.
Lemma lem78578 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78579 (m : nat) (n : nat) (p : nat) : (term60 m n p) = ((term28 m n p) = (term28 m n p)).
Proof. exact (@lem78578 ((term28 m n p) = (term28 m n p))). Qed.
Lemma lem78580 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem78579 m n p) (@lem78576 m n p)). Qed.
Lemma lem78598 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem78599 (y : nat) (x : nat) (z : nat) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem78598 (y = z) (term64 x z)). Qed.
Lemma lem78609 (x : nat) (y : nat) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem78610 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem78609 x y) (@lem78599 y x z)). Qed.
Lemma lem78614 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem78615 (y : nat) (x : nat) (z : nat) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem78614 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem78637 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem78610 y x z) (@lem78615 y x z)). Qed.
Lemma lem78638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem78639 (y : nat) (x : nat) (z : nat) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem78638) (@lem78637 y x z)). Qed.
Lemma lem78661 (y : nat) (x : nat) (z : nat) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem78662 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem78639 y x z) (@lem78661 y x z)). Qed.
Lemma lem78664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem78665 (x : Prop) : (x = x) = True.
Proof. exact (@lem78664 Prop x). Qed.
Lemma lem78666 (y : nat) (x : nat) (z : nat) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem78665 (term68 y x z)). Qed.
Lemma lem78667 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem78662 y x z) (@lem78666 y x z)). Qed.
Lemma lem78668 (y : nat) (x : nat) (z : nat) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem78667 y x z)). Qed.
Lemma lem78669 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem78668 y x z) (@lem0)). Qed.
Lemma lem78670 (y : nat) (x : nat) (z : nat) : term68 y x z.
Proof. exact (EQ_MP (@lem78669 y x z) (@lem78564 x y z)). Qed.
Lemma lem78672 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem78673 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem78672 (term73 y x z) (y = z)). Qed.
Lemma lem78675 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem78676 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem78675 (term64 x y) (term64 x z)). Qed.
Lemma lem78678 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78679 (x : nat) (y : nat) : (term79 x y) = (x = y).
Proof. exact (@lem78678 (x = y)). Qed.
Lemma lem78680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem78681 (x : nat) (y : nat) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem78680) (@lem78679 x y)). Qed.
Lemma lem78683 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78684 (x : nat) (z : nat) : (term79 x z) = (x = z).
Proof. exact (@lem78683 (x = z)). Qed.
Lemma lem78685 (y : nat) (x : nat) (z : nat) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem78681 x y) (@lem78684 x z)). Qed.
Lemma lem78686 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem78676 y x z) (@lem78685 y x z)). Qed.
Lemma lem78687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem78688 (y : nat) (x : nat) (z : nat) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem78687) (@lem78686 y x z)). Qed.
Lemma lem78689 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem78690 (x : nat) (y : nat) (z : nat) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem78688 y x z) (@lem78689 y z)). Qed.
Lemma lem78691 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem78673 x y z) (@lem78690 x y z)). Qed.
Lemma lem78693 (m : nat) (n : nat) (p : nat) (h1 : term10) : term86 m n p.
Proof. exact (conj (@lem78572 m n p h1) (@lem78580 m n p)). Qed.
Lemma lem78695 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem78691 x y z) (@lem78670 y x z)). Qed.
Lemma lem78696 (m : nat) (n : nat) (p : nat) : term87 m n p.
Proof. exact (@lem78695 (term28 m n p) (term29 m n p) (term28 m n p)). Qed.
Lemma lem78699 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (@lem78696 m n p (@lem78693 m n p h1)). Qed.
Lemma lem78700 (m : nat) (n : nat) (p : nat) (h1 : term10) : term88 m n p.
Proof. exact (fun h0 : term46 m n p => @lem78699 m n p h1). Qed.
Lemma lem78702 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78703 (m : nat) (n : nat) (p : nat) : (term88 m n p) = ((term29 m n p) = (term28 m n p)).
Proof. exact (@lem78702 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem78704 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem78703 m n p) (@lem78700 m n p h1)). Qed.
Lemma lem78707 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem78709 (m : nat) (n : nat) (p : nat) : (term46 m n p) = (term89 m n p).
Proof. exact (@lem78707 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem78712 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term89 m n p.
Proof. exact (EQ_MP (@lem78709 m n p) (@lem78500 m n p h1)). Qed.
Lemma lem78715 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (@lem78712 m n p h2 (@lem78704 m n p h1)). Qed.
Lemma lem78716 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : term56.
Proof. exact (fun h0 : ~ False => @lem78715 m n p h1 h2). Qed.
Lemma lem78718 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78719 : term56 = False.
Proof. exact (@lem78718 False). Qed.
Lemma lem78720 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem78719) (@lem78716 m n p h1 h2)). Qed.
Lemma lem78721 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem78722 (_2179 : nat) (_2181 : nat) (h1 : _2179 = _2181) : _2179 = _2181.
Proof. exact (h1). Qed.
Lemma lem78723 (_2180 : nat) (_2182 : nat) (h1 : _2180 = _2182) : _2180 = _2182.
Proof. exact (h1). Qed.
Lemma lem78724 (_2179 : nat) (_2181 : nat) (h1 : _2179 = _2181) : (Nat.add _2179) = (Nat.add _2181).
Proof. exact (MK_COMB (@lem78721) (@lem78722 _2179 _2181 h1)). Qed.
Lemma lem78725 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) (h1 : _2179 = _2181) (h2 : _2180 = _2182) : (Nat.add _2179 _2180) = (Nat.add _2181 _2182).
Proof. exact (MK_COMB (@lem78724 _2179 _2181 h1) (@lem78723 _2180 _2182 h2)). Qed.
Lemma lem78726 (_2180 : nat) (_2182 : nat) (_2179 : nat) (_2181 : nat) (h1 : _2179 = _2181) : term90 _2179 _2180 _2181 _2182.
Proof. exact (fun h0 : _2180 = _2182 => @lem78725 _2179 _2181 _2180 _2182 h1 h0). Qed.
Lemma lem78728 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem78729 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : (term90 _2179 _2180 _2181 _2182) = (term92 _2179 _2180 _2181 _2182).
Proof. exact (@lem78728 (_2180 = _2182) ((Nat.add _2179 _2180) = (Nat.add _2181 _2182))). Qed.
Lemma lem78730 (_2180 : nat) (_2182 : nat) (_2179 : nat) (_2181 : nat) (h1 : _2179 = _2181) : term92 _2179 _2180 _2181 _2182.
Proof. exact (EQ_MP (@lem78729 _2179 _2180 _2181 _2182) (@lem78726 _2180 _2182 _2179 _2181 h1)). Qed.
Lemma lem78731 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : term93 _2179 _2180 _2181 _2182.
Proof. exact (fun h0 : _2179 = _2181 => @lem78730 _2180 _2182 _2179 _2181 h0). Qed.
Lemma lem78733 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem78734 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : (term93 _2179 _2180 _2181 _2182) = (term94 _2179 _2180 _2181 _2182).
Proof. exact (@lem78733 (_2179 = _2181) (term92 _2179 _2180 _2181 _2182)). Qed.
Lemma lem78735 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : term94 _2179 _2180 _2181 _2182.
Proof. exact (EQ_MP (@lem78734 _2179 _2180 _2181 _2182) (@lem78731 _2179 _2180 _2181 _2182)). Qed.
Lemma lem78737 (x : nat) (y : nat) (z : nat) : term57 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem78739 (_2167 : nat) (_2166 : nat) (h1 : term38) : (Nat.add _2166 _2167) = (Nat.add _2167 _2166).
Proof. exact (EQ_MP (@lem78478 _2167 _2166) (@lem78477 _2166 _2167 h1)). Qed.
Lemma lem78740 (m : nat) (n : nat) (p : nat) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (@lem78739 m (Nat.add n p) h1). Qed.
Lemma lem78741 (m : nat) (n : nat) (p : nat) (h1 : term38) : term95 m n p.
Proof. exact (fun h0 : term96 m n p => @lem78740 m n p h1). Qed.
Lemma lem78743 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78744 (m : nat) (n : nat) (p : nat) : (term95 m n p) = ((term29 n p m) = (term28 m n p)).
Proof. exact (@lem78743 ((term29 n p m) = (term28 m n p))). Qed.
Lemma lem78745 (m : nat) (n : nat) (p : nat) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (EQ_MP (@lem78744 m n p) (@lem78741 m n p h1)). Qed.
Lemma lem78747 (_2168 : nat) (_2169 : nat) (_2170 : nat) (h1 : term10) : (term28 _2168 _2169 _2170) = (term29 _2168 _2169 _2170).
Proof. exact (EQ_MP (@lem78487 _2168 _2169 _2170) (@lem78486 _2168 _2169 _2170 h1)). Qed.
Lemma lem78748 (n : nat) (p : nat) (m : nat) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (@lem78747 n p m h1). Qed.
Lemma lem78749 (n : nat) (p : nat) (m : nat) (h1 : term10) : term58 n p m.
Proof. exact (fun h0 : term59 n p m => @lem78748 n p m h1). Qed.
Lemma lem78751 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78752 (n : nat) (p : nat) (m : nat) : (term58 n p m) = ((term28 n p m) = (term29 n p m)).
Proof. exact (@lem78751 ((term28 n p m) = (term29 n p m))). Qed.
Lemma lem78753 (n : nat) (p : nat) (m : nat) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (EQ_MP (@lem78752 n p m) (@lem78749 n p m h1)). Qed.
Lemma lem78755 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem78756 (n : nat) : n = n.
Proof. exact (@lem78755 n). Qed.
Lemma lem78757 (n : nat) : term97 n.
Proof. exact (fun h0 : term98 n => @lem78756 n). Qed.
Lemma lem78759 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78760 (n : nat) : (term97 n) = (n = n).
Proof. exact (@lem78759 (n = n)). Qed.
Lemma lem78761 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem78760 n) (@lem78757 n)). Qed.
Lemma lem78763 (_2167 : nat) (_2166 : nat) (h1 : term38) : (Nat.add _2166 _2167) = (Nat.add _2167 _2166).
Proof. exact (EQ_MP (@lem78478 _2167 _2166) (@lem78477 _2166 _2167 h1)). Qed.
Lemma lem78764 (m : nat) (p : nat) (h1 : term38) : (Nat.add p m) = (Nat.add m p).
Proof. exact (@lem78763 m p h1). Qed.
Lemma lem78765 (m : nat) (p : nat) (h1 : term38) : term53 m p.
Proof. exact (fun h0 : term45 m p => @lem78764 m p h1). Qed.
Lemma lem78767 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78768 (m : nat) (p : nat) : (term53 m p) = ((Nat.add p m) = (Nat.add m p)).
Proof. exact (@lem78767 ((Nat.add p m) = (Nat.add m p))). Qed.
Lemma lem78769 (m : nat) (p : nat) (h1 : term38) : (Nat.add p m) = (Nat.add m p).
Proof. exact (EQ_MP (@lem78768 m p) (@lem78765 m p h1)). Qed.
Lemma lem78787 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem78788 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term92 _2179 _2180 _2181 _2182) = (term99 _2179 _2181 _2180 _2182).
Proof. exact (@lem78787 ((Nat.add _2179 _2180) = (Nat.add _2181 _2182)) (term64 _2180 _2182)). Qed.
Lemma lem78798 (_2179 : nat) (_2181 : nat) : (term65 _2179 _2181) = (term65 _2179 _2181).
Proof. exact (eq_refl (term65 _2179 _2181)). Qed.
Lemma lem78799 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term94 _2179 _2180 _2181 _2182) = (term100 _2179 _2181 _2180 _2182).
Proof. exact (MK_COMB (@lem78798 _2179 _2181) (@lem78788 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78803 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem78804 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term100 _2179 _2181 _2180 _2182) = (term101 _2179 _2181 _2180 _2182).
Proof. exact (@lem78803 ((Nat.add _2179 _2180) = (Nat.add _2181 _2182)) (term64 _2179 _2181) (term64 _2180 _2182)). Qed.
Lemma lem78826 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term94 _2179 _2180 _2181 _2182) = (term101 _2179 _2181 _2180 _2182).
Proof. exact (TRANS (@lem78799 _2179 _2181 _2180 _2182) (@lem78804 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem78828 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term102 _2179 _2180 _2181 _2182) = (term103 _2179 _2181 _2180 _2182).
Proof. exact (MK_COMB (@lem78827) (@lem78826 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78850 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term101 _2179 _2181 _2180 _2182) = (term101 _2179 _2181 _2180 _2182).
Proof. exact (eq_refl (term101 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78851 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : ((term94 _2179 _2180 _2181 _2182) = (term101 _2179 _2181 _2180 _2182)) = ((term101 _2179 _2181 _2180 _2182) = (term101 _2179 _2181 _2180 _2182)).
Proof. exact (MK_COMB (@lem78828 _2179 _2181 _2180 _2182) (@lem78850 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78853 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem78854 (x : Prop) : (x = x) = True.
Proof. exact (@lem78853 Prop x). Qed.
Lemma lem78855 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : ((term101 _2179 _2181 _2180 _2182) = (term101 _2179 _2181 _2180 _2182)) = True.
Proof. exact (@lem78854 (term101 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78856 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : ((term94 _2179 _2180 _2181 _2182) = (term101 _2179 _2181 _2180 _2182)) = True.
Proof. exact (TRANS (@lem78851 _2179 _2181 _2180 _2182) (@lem78855 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78857 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : True = ((term94 _2179 _2180 _2181 _2182) = (term101 _2179 _2181 _2180 _2182)).
Proof. exact (SYM (@lem78856 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78858 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term94 _2179 _2180 _2181 _2182) = (term101 _2179 _2181 _2180 _2182).
Proof. exact (EQ_MP (@lem78857 _2179 _2181 _2180 _2182) (@lem0)). Qed.
Lemma lem78859 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : term101 _2179 _2181 _2180 _2182.
Proof. exact (EQ_MP (@lem78858 _2179 _2181 _2180 _2182) (@lem78735 _2179 _2180 _2181 _2182)). Qed.
Lemma lem78861 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem78862 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : (term101 _2179 _2181 _2180 _2182) = (term104 _2179 _2180 _2181 _2182).
Proof. exact (@lem78861 (term105 _2179 _2181 _2180 _2182) ((Nat.add _2179 _2180) = (Nat.add _2181 _2182))). Qed.
Lemma lem78864 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem78865 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term106 _2179 _2181 _2180 _2182) = (term107 _2179 _2181 _2180 _2182).
Proof. exact (@lem78864 (term64 _2179 _2181) (term64 _2180 _2182)). Qed.
Lemma lem78867 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78868 (_2179 : nat) (_2181 : nat) : (term79 _2179 _2181) = (_2179 = _2181).
Proof. exact (@lem78867 (_2179 = _2181)). Qed.
Lemma lem78869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem78870 (_2179 : nat) (_2181 : nat) : (term80 _2179 _2181) = (term81 _2179 _2181).
Proof. exact (MK_COMB (@lem78869) (@lem78868 _2179 _2181)). Qed.
Lemma lem78872 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78873 (_2180 : nat) (_2182 : nat) : (term79 _2180 _2182) = (_2180 = _2182).
Proof. exact (@lem78872 (_2180 = _2182)). Qed.
Lemma lem78874 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term107 _2179 _2181 _2180 _2182) = (term108 _2179 _2181 _2180 _2182).
Proof. exact (MK_COMB (@lem78870 _2179 _2181) (@lem78873 _2180 _2182)). Qed.
Lemma lem78875 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term106 _2179 _2181 _2180 _2182) = (term108 _2179 _2181 _2180 _2182).
Proof. exact (TRANS (@lem78865 _2179 _2181 _2180 _2182) (@lem78874 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem78877 (_2179 : nat) (_2181 : nat) (_2180 : nat) (_2182 : nat) : (term109 _2179 _2181 _2180 _2182) = (term110 _2179 _2181 _2180 _2182).
Proof. exact (MK_COMB (@lem78876) (@lem78875 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78878 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : ((Nat.add _2179 _2180) = (Nat.add _2181 _2182)) = ((Nat.add _2179 _2180) = (Nat.add _2181 _2182)).
Proof. exact (eq_refl ((Nat.add _2179 _2180) = (Nat.add _2181 _2182))). Qed.
Lemma lem78879 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : (term104 _2179 _2180 _2181 _2182) = (term111 _2179 _2180 _2181 _2182).
Proof. exact (MK_COMB (@lem78877 _2179 _2181 _2180 _2182) (@lem78878 _2179 _2180 _2181 _2182)). Qed.
Lemma lem78880 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : (term101 _2179 _2181 _2180 _2182) = (term111 _2179 _2180 _2181 _2182).
Proof. exact (TRANS (@lem78862 _2179 _2180 _2181 _2182) (@lem78879 _2179 _2180 _2181 _2182)). Qed.
Lemma lem78882 (n : nat) (m : nat) (p : nat) (h1 : term38) : term112 n m p.
Proof. exact (conj (@lem78761 n) (@lem78769 m p h1)). Qed.
Lemma lem78884 (_2179 : nat) (_2180 : nat) (_2181 : nat) (_2182 : nat) : term111 _2179 _2180 _2181 _2182.
Proof. exact (EQ_MP (@lem78880 _2179 _2180 _2181 _2182) (@lem78859 _2179 _2181 _2180 _2182)). Qed.
Lemma lem78885 (n : nat) (m : nat) (p : nat) : term113 n m p.
Proof. exact (@lem78884 n (Nat.add p m) n (Nat.add m p)). Qed.
Lemma lem78888 (n : nat) (m : nat) (p : nat) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (@lem78885 n m p (@lem78882 n m p h1)). Qed.
Lemma lem78889 (n : nat) (m : nat) (p : nat) (h1 : term38) : term114 n m p.
Proof. exact (fun h0 : term115 n m p => @lem78888 n m p h1). Qed.
Lemma lem78891 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem78892 (n : nat) (m : nat) (p : nat) : (term114 n m p) = ((term28 n p m) = (term28 n m p)).
Proof. exact (@lem78891 ((term28 n p m) = (term28 n m p))). Qed.
Lemma lem78893 (n : nat) (m : nat) (p : nat) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem78892 n m p) (@lem78889 n m p h1)). Qed.
Lemma lem78911 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem78912 (y : nat) (x : nat) (z : nat) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem78911 (y = z) (term64 x z)). Qed.
Lemma lem78922 (x : nat) (y : nat) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem78923 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem78922 x y) (@lem78912 y x z)). Qed.
Lemma lem78927 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem78928 (y : nat) (x : nat) (z : nat) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem78927 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem78950 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem78923 y x z) (@lem78928 y x z)). Qed.
Lemma lem78951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem78952 (y : nat) (x : nat) (z : nat) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem78951) (@lem78950 y x z)). Qed.
Lemma lem78974 (y : nat) (x : nat) (z : nat) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem78975 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem78952 y x z) (@lem78974 y x z)). Qed.
Lemma lem78977 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem78978 (x : Prop) : (x = x) = True.
Proof. exact (@lem78977 Prop x). Qed.
Lemma lem78979 (y : nat) (x : nat) (z : nat) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem78978 (term68 y x z)). Qed.
Lemma lem78980 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem78975 y x z) (@lem78979 y x z)). Qed.
Lemma lem78981 (y : nat) (x : nat) (z : nat) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem78980 y x z)). Qed.
Lemma lem78982 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem78981 y x z) (@lem0)). Qed.
Lemma lem78983 (y : nat) (x : nat) (z : nat) : term68 y x z.
Proof. exact (EQ_MP (@lem78982 y x z) (@lem78737 x y z)). Qed.
Lemma lem78985 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem78986 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem78985 (term73 y x z) (y = z)). Qed.
Lemma lem78988 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem78989 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem78988 (term64 x y) (term64 x z)). Qed.
Lemma lem78991 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78992 (x : nat) (y : nat) : (term79 x y) = (x = y).
Proof. exact (@lem78991 (x = y)). Qed.
Lemma lem78993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem78994 (x : nat) (y : nat) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem78993) (@lem78992 x y)). Qed.
Lemma lem78996 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem78997 (x : nat) (z : nat) : (term79 x z) = (x = z).
Proof. exact (@lem78996 (x = z)). Qed.
Lemma lem78998 (y : nat) (x : nat) (z : nat) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem78994 x y) (@lem78997 x z)). Qed.
Lemma lem78999 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem78989 y x z) (@lem78998 y x z)). Qed.
Lemma lem79000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79001 (y : nat) (x : nat) (z : nat) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem79000) (@lem78999 y x z)). Qed.
Lemma lem79002 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem79003 (x : nat) (y : nat) (z : nat) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem79001 y x z) (@lem79002 y z)). Qed.
Lemma lem79004 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem78986 x y z) (@lem79003 x y z)). Qed.
Lemma lem79006 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term116 n m p.
Proof. exact (conj (@lem78753 n p m h1) (@lem78893 n m p h2)). Qed.
Lemma lem79008 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem79004 x y z) (@lem78983 y x z)). Qed.
Lemma lem79009 (n : nat) (m : nat) (p : nat) : term117 n m p.
Proof. exact (@lem79008 (term28 n p m) (term29 n p m) (term28 n m p)). Qed.
Lemma lem79012 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (@lem79009 n m p (@lem79006 n m p h1 h2)). Qed.
Lemma lem79013 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term118 n m p.
Proof. exact (fun h0 : term119 n m p => @lem79012 n m p h1 h2). Qed.
Lemma lem79015 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem79016 (n : nat) (m : nat) (p : nat) : (term118 n m p) = ((term29 n p m) = (term28 n m p)).
Proof. exact (@lem79015 ((term29 n p m) = (term28 n m p))). Qed.
Lemma lem79017 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem79016 n m p) (@lem79013 n m p h1 h2)). Qed.
Lemma lem79018 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term120 n m p.
Proof. exact (conj (@lem78745 m n p h2) (@lem79017 n m p h1 h2)). Qed.
Lemma lem79020 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem79004 x y z) (@lem78983 y x z)). Qed.
Lemma lem79021 (n : nat) (m : nat) (p : nat) : term121 n m p.
Proof. exact (@lem79020 (term29 n p m) (term28 m n p) (term28 n m p)). Qed.
Lemma lem79024 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (@lem79021 n m p (@lem79018 n m p h1 h2)). Qed.
Lemma lem79025 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term122 n m p.
Proof. exact (fun h0 : term47 n m p => @lem79024 n m p h1 h2). Qed.
Lemma lem79027 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem79028 (n : nat) (m : nat) (p : nat) : (term122 n m p) = ((term28 m n p) = (term28 n m p)).
Proof. exact (@lem79027 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem79029 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (EQ_MP (@lem79028 n m p) (@lem79025 n m p h1 h2)). Qed.
Lemma lem79032 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem79034 (n : nat) (m : nat) (p : nat) : (term47 n m p) = (term123 n m p).
Proof. exact (@lem79032 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem79037 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term123 n m p.
Proof. exact (EQ_MP (@lem79034 n m p) (@lem78506 n m p h1)). Qed.
Lemma lem79040 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (@lem79037 n m p h3 (@lem79029 n m p h1 h2)). Qed.
Lemma lem79041 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term56.
Proof. exact (fun h0 : ~ False => @lem79040 n m p h1 h2 h3). Qed.
Lemma lem79043 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem79044 : term56 = False.
Proof. exact (@lem79043 False). Qed.
Lemma lem79045 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79044) (@lem79041 n m p h1 h2 h3)). Qed.
Lemma lem79046 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem79045 n m p h1 h2 h3) (fun h4 : False => @lem78506 n m p h3)). Qed.
Lemma lem79047 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79046 n m p h1 h2 h3) (@lem78506 n m p h3)). Qed.
Lemma lem79048 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem78720 m n p h1 h2) (fun h3 : False => @lem78500 m n p h2)). Qed.
Lemma lem79049 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem79048 m n p h1 h2) (@lem78500 m n p h2)). Qed.
Lemma lem79050 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem78547 n m h1 h2) (fun h3 : False => @lem78494 n m h2)). Qed.
Lemma lem79051 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem79050 n m h1 h2) (@lem78494 n m h2)). Qed.
Lemma lem79052 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem79047 n m p h1 h2 h3) (fun h4 : False => @lem78443 n m p h3)). Qed.
Lemma lem79053 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79052 n m p h1 h2 h3) (@lem78443 n m p h3)). Qed.
Lemma lem79054 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem79049 m n p h1 h2) (fun h3 : False => @lem78416 m n p h2)). Qed.
Lemma lem79055 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem79054 m n p h1 h2) (@lem78416 m n p h2)). Qed.
Lemma lem79056 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem79051 n m h1 h2) (fun h3 : False => @lem78389 n m h2)). Qed.
Lemma lem79057 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem79056 n m h1 h2) (@lem78389 n m h2)). Qed.
Lemma lem79058 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem79053 n m p h1 h2 h3) (fun h4 : False => @lem78443 n m p h3)). Qed.
Lemma lem79059 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79058 n m p h1 h2 h3) (@lem78443 n m p h3)). Qed.
Lemma lem79060 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem79059 n m p h1 h2 h3) (fun h4 : False => @lem78439 h1)). Qed.
Lemma lem79061 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79060 n m p h1 h2 h3) (@lem78439 h1)). Qed.
Lemma lem79062 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem79061 n m p h1 h2 h3) (fun h4 : False => @lem78426 h2)). Qed.
Lemma lem79063 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem79062 n m p h1 h2 h3) (@lem78426 h2)). Qed.
Lemma lem79064 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem79055 m n p h1 h2) (fun h3 : False => @lem78416 m n p h2)). Qed.
Lemma lem79065 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem79064 m n p h1 h2) (@lem78416 m n p h2)). Qed.
Lemma lem79066 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem79065 m n p h1 h2) (fun h3 : False => @lem78412 h1)). Qed.
Lemma lem79067 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem79066 m n p h1 h2) (@lem78412 h1)). Qed.
Lemma lem79068 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem79057 n m h1 h2) (fun h3 : False => @lem78389 n m h2)). Qed.
Lemma lem79069 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem79068 n m h1 h2) (@lem78389 n m h2)). Qed.
Lemma lem79070 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : term38 = False.
Proof. exact (prop_ext (fun h3 : term38 => @lem79069 n m h1 h2) (fun h3 : False => @lem78372 h1)). Qed.
Lemma lem79071 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem79070 n m h1 h2) (@lem78372 h1)). Qed.
Lemma lem79072 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term40 n m p) : False.
Proof. exact (or_elim (@lem78360 n m p h3) (fun h0 : term46 m n p => @lem79067 m n p h1 h0) (fun h0 : term47 n m p => @lem79063 n m p h1 h2 h0)). Qed.
Lemma lem79073 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (or_elim (@lem78307 n m p h3) (fun h0 : term45 n m => @lem79071 n m h2 h0) (fun h0 : term40 n m p => @lem79072 n m p h1 h2 h0)). Qed.
Lemma lem79074 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem79073 n m p h1 h2 h3) (fun h4 : False => @lem78358 h1)). Qed.
Lemma lem79075 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem79074 n m p h1 h2 h3) (@lem78358 h1)). Qed.
Lemma lem79076 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem79075 n m p h1 h2 h3) (fun h4 : False => @lem78327 h2)). Qed.
Lemma lem79077 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem79076 n m p h1 h2 h3) (@lem78327 h2)). Qed.
Lemma lem79078 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem79077 n m p h1 h2 h3) (fun h4 : False => @lem78239 h1)). Qed.
Lemma lem79079 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem79078 n m p h1 h2 h3) (@lem78239 h1)). Qed.
Lemma lem79080 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem79079 n m p h1 h2 h3) (fun h4 : False => @lem78212 h2)). Qed.
Lemma lem79081 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem79080 n m p h1 h2 h3) (@lem78212 h2)). Qed.
Lemma lem79082 (n : nat) (m : nat) (p : nat) (h1 : term38) (h2 : term3 n m p) : term8.
Proof. exact (fun h0 : term10 => @lem79081 n m p h0 h1 h2). Qed.
Lemma lem79083 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem79084 (n : nat) (m : nat) (p : nat) (h1 : term38) (h2 : term3 n m p) : term9.
Proof. exact (EQ_MP (@lem79083) (@lem79082 n m p h1 h2)). Qed.
Lemma lem79085 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term13.
Proof. exact (fun h0 : term38 => @lem79084 n m p h0 h1). Qed.
Lemma lem79086 (n : nat) (m : nat) (p : nat) : term15 n m p.
Proof. exact (fun h0 : term3 n m p => @lem79085 n m p h0). Qed.
Lemma lem79091 (m : nat) (p : nat) : term19 m p.
Proof. exact (fun n : nat => @lem79086 n m p). Qed.
Lemma lem79096 (p : nat) : term23 p.
Proof. exact (fun m : nat => @lem79091 m p). Qed.
Lemma lem79101 : term27.
Proof. exact (fun p : nat => @lem79096 p). Qed.
Lemma lem79102 : term26.
Proof. exact (EQ_MP (@lem78171) (@lem79101)). Qed.
Lemma lem79103 (p : nat) : term124 p.
Proof. exact (@lem79102 p). Qed.
Lemma lem79104 (p : nat) : (term124 p) = (term22 p).
Proof. exact (eq_refl (term124 p)). Qed.
Lemma lem79105 (p : nat) : term22 p.
Proof. exact (EQ_MP (@lem79104 p) (@lem79103 p)). Qed.
Lemma lem79106 (p : nat) (m : nat) : term125 p m.
Proof. exact (@lem79105 p m). Qed.
Lemma lem79107 (m : nat) (p : nat) : (term125 p m) = (term18 m p).
Proof. exact (eq_refl (term125 p m)). Qed.
Lemma lem79108 (m : nat) (p : nat) : term18 m p.
Proof. exact (EQ_MP (@lem79107 m p) (@lem79106 p m)). Qed.
Lemma lem79109 (m : nat) (p : nat) (n : nat) : term126 m p n.
Proof. exact (@lem79108 m p n). Qed.
Lemma lem79110 (n : nat) (m : nat) (p : nat) : (term126 m p n) = (term4 n m p).
Proof. exact (eq_refl (term126 m p n)). Qed.
Lemma lem79111 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (EQ_MP (@lem79110 n m p) (@lem79109 m p n)). Qed.
Lemma lem79113 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem77990 n m p (@lem79111 n m p)). Qed.
Lemma lem79114 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term12.
Proof. exact (@lem79113 n m p (@lem77975 n m p h1)). Qed.
Lemma lem79115 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term8.
Proof. exact (@lem79114 n m p h1 (@lem77775)). Qed.
Lemma lem79116 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : False.
Proof. exact (@lem79115 n m p h1 (@lem77960)). Qed.
Lemma lem79117 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : (term3 n m p) = False.
Proof. exact (prop_ext (fun h2 : term3 n m p => @lem79116 n m p h1) (fun h2 : False => @lem77975 n m p h1)). Qed.
Lemma lem79118 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem79117 n m p h1) (@lem77975 n m p h1)). Qed.
Lemma lem79119 (n : nat) (m : nat) (p : nat) : term2 n m p.
Proof. exact (fun h0 : term3 n m p => @lem79118 n m p h0). Qed.
Lemma lem79120 (n : nat) (m : nat) (p : nat) : term1 n m p.
Proof. exact (EQ_MP (@lem77974 n m p) (@lem79119 n m p)). Qed.
