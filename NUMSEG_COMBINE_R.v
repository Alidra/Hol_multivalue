Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_COMBINE_R_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_UNION_spec.
Require Import numseg_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5329324 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5329325 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5329324 _83095 p). Qed.
Lemma lem5329326 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5329327 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5329326 _83095 p) (@lem5329325 _83095 p)). Qed.
Lemma lem5329328 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5329327 _83095 p x). Qed.
Lemma lem5329329 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5329338 (m : nat) : term5 m.
Proof. exact (@lem5329077 m). Qed.
Lemma lem5329339 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5329340 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem5329339 m) (@lem5329338 m)). Qed.
Lemma lem5329341 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem5329340 m n). Qed.
Lemma lem5329342 (m : nat) (n : nat) : (term7 m n) = ((dotdot m n) = (term8 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem5329344 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem5329345 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem5329346 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem5329345 A s) (@lem5329344 A s)). Qed.
Lemma lem5329347 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem5329346 A s t). Qed.
Lemma lem5329348 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem5329349 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem5329348 A s t) (@lem5329347 A s t)). Qed.
Lemma lem5329350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem5329349 A s t x). Qed.
Lemma lem5329351 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem5329353 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5329354 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem5329355 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem5329354 A s) (@lem5329353 A s)). Qed.
Lemma lem5329356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem5329355 A s t). Qed.
Lemma lem5329357 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem5329378 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem5329357 A s t) (@lem5329356 A s t)). Qed.
Lemma lem5329379 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term20 s t).
Proof. exact (@lem5329378 nat s t). Qed.
Lemma lem5329380 (p : nat) (m : nat) (n : nat) : ((term21 m p n) = (dotdot m n)) = (term22 p m n).
Proof. exact (@lem5329379 (term21 m p n) (dotdot m n)). Qed.
Lemma lem5329390 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem5329351 A s x t) (@lem5329350 A s t x)). Qed.
Lemma lem5329391 (s : nat -> Prop) (x : nat) (t : nat -> Prop) : (term23 x s t) = (term24 s x t).
Proof. exact (@lem5329390 nat s x t). Qed.
Lemma lem5329392 (m : nat) (x : nat) (p : nat) (n : nat) : (term25 x m p n) = (term26 m x p n).
Proof. exact (@lem5329391 (dotdot m p) x (term27 p n)). Qed.
Lemma lem5329396 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5329342 m n) (@lem5329341 m n)). Qed.
Lemma lem5329397 (m : nat) (p : nat) : (dotdot m p) = (term8 m p).
Proof. exact (@lem5329396 m p). Qed.
Lemma lem5329404 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329405 (x : nat) (m : nat) (p : nat) : (term28 x m p) = (term29 x m p).
Proof. exact (MK_COMB (@lem5329404 x) (@lem5329397 m p)). Qed.
Lemma lem5329407 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5329329 _83095 p x) (@lem5329328 _83095 p x)). Qed.
Lemma lem5329408 (p : nat -> Prop) (x : nat) : (term30 x p) = (p x).
Proof. exact (@lem5329407 nat p x). Qed.
Lemma lem5329409 (m : nat) (p : nat) (x : nat) : (term31 x m p) = (term32 m p x).
Proof. exact (@lem5329408 (term33 m p) x). Qed.
Lemma lem5329410 (m : nat) (x : nat) (p : nat) : (term32 m p x) = (term34 m x p).
Proof. exact (eq_refl (term32 m p x)). Qed.
Lemma lem5329411 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5329412 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (p : nat) : (term35 GEN_PVAR_229 m p x) = (term36 GEN_PVAR_229 m x p).
Proof. exact (MK_COMB (@lem5329411 GEN_PVAR_229) (@lem5329410 m x p)). Qed.
Lemma lem5329413 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5329414 (GEN_PVAR_229 : nat) (m : nat) (p : nat) (x : nat) : (term37 GEN_PVAR_229 m p x) = (term38 GEN_PVAR_229 m p x).
Proof. exact (MK_COMB (@lem5329412 GEN_PVAR_229 m x p) (@lem5329413 x)). Qed.
Lemma lem5329415 (GEN_PVAR_229 : nat) (m : nat) (p : nat) : (term39 GEN_PVAR_229 m p) = (term40 GEN_PVAR_229 m p).
Proof. exact (fun_ext (fun x : nat => @lem5329414 GEN_PVAR_229 m p x)). Qed.
Lemma lem5329416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5329417 (GEN_PVAR_229 : nat) (m : nat) (p : nat) : (term41 GEN_PVAR_229 m p) = (term42 GEN_PVAR_229 m p).
Proof. exact (MK_COMB (@lem5329416) (@lem5329415 GEN_PVAR_229 m p)). Qed.
Lemma lem5329418 (m : nat) (p : nat) : (term43 m p) = (term44 m p).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5329417 GEN_PVAR_229 m p)). Qed.
Lemma lem5329419 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5329420 (m : nat) (p : nat) : (term45 m p) = (term8 m p).
Proof. exact (MK_COMB (@lem5329419) (@lem5329418 m p)). Qed.
Lemma lem5329421 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329422 (x : nat) (m : nat) (p : nat) : (term31 x m p) = (term29 x m p).
Proof. exact (MK_COMB (@lem5329421 x) (@lem5329420 m p)). Qed.
Lemma lem5329423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329424 (x : nat) (m : nat) (p : nat) : (term46 x m p) = (term47 x m p).
Proof. exact (MK_COMB (@lem5329423) (@lem5329422 x m p)). Qed.
Lemma lem5329425 (m : nat) (x : nat) (p : nat) : (term32 m p x) = (term34 m x p).
Proof. exact (eq_refl (term32 m p x)). Qed.
Lemma lem5329426 (m : nat) (x : nat) (p : nat) : ((term31 x m p) = (term32 m p x)) = ((term29 x m p) = (term34 m x p)).
Proof. exact (MK_COMB (@lem5329424 x m p) (@lem5329425 m x p)). Qed.
Lemma lem5329427 (m : nat) (x : nat) (p : nat) : (term29 x m p) = (term34 m x p).
Proof. exact (EQ_MP (@lem5329426 m x p) (@lem5329409 m p x)). Qed.
Lemma lem5329430 (m : nat) (x : nat) (p : nat) : (term28 x m p) = (term34 m x p).
Proof. exact (TRANS (@lem5329405 x m p) (@lem5329427 m x p)). Qed.
Lemma lem5329431 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329432 (m : nat) (x : nat) (p : nat) : (term48 x m p) = (term49 m x p).
Proof. exact (MK_COMB (@lem5329431) (@lem5329430 m x p)). Qed.
Lemma lem5329434 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5329342 m n) (@lem5329341 m n)). Qed.
Lemma lem5329435 (p : nat) (n : nat) : (term27 p n) = (term50 p n).
Proof. exact (@lem5329434 (term51 p) n). Qed.
Lemma lem5329442 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329443 (x : nat) (p : nat) (n : nat) : (term52 x p n) = (term53 x p n).
Proof. exact (MK_COMB (@lem5329442 x) (@lem5329435 p n)). Qed.
Lemma lem5329445 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5329329 _83095 p x) (@lem5329328 _83095 p x)). Qed.
Lemma lem5329446 (p : nat -> Prop) (x : nat) : (term30 x p) = (p x).
Proof. exact (@lem5329445 nat p x). Qed.
Lemma lem5329447 (p : nat) (n : nat) (x : nat) : (term54 x p n) = (term55 p n x).
Proof. exact (@lem5329446 (term56 p n) x). Qed.
Lemma lem5329448 (p : nat) (x : nat) (n : nat) : (term55 p n x) = (term57 p x n).
Proof. exact (eq_refl (term55 p n x)). Qed.
Lemma lem5329449 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5329450 (GEN_PVAR_229 : nat) (p : nat) (x : nat) (n : nat) : (term58 GEN_PVAR_229 p n x) = (term59 GEN_PVAR_229 p x n).
Proof. exact (MK_COMB (@lem5329449 GEN_PVAR_229) (@lem5329448 p x n)). Qed.
Lemma lem5329451 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5329452 (GEN_PVAR_229 : nat) (p : nat) (n : nat) (x : nat) : (term60 GEN_PVAR_229 p n x) = (term61 GEN_PVAR_229 p n x).
Proof. exact (MK_COMB (@lem5329450 GEN_PVAR_229 p x n) (@lem5329451 x)). Qed.
Lemma lem5329453 (GEN_PVAR_229 : nat) (p : nat) (n : nat) : (term62 GEN_PVAR_229 p n) = (term63 GEN_PVAR_229 p n).
Proof. exact (fun_ext (fun x : nat => @lem5329452 GEN_PVAR_229 p n x)). Qed.
Lemma lem5329454 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5329455 (GEN_PVAR_229 : nat) (p : nat) (n : nat) : (term64 GEN_PVAR_229 p n) = (term65 GEN_PVAR_229 p n).
Proof. exact (MK_COMB (@lem5329454) (@lem5329453 GEN_PVAR_229 p n)). Qed.
Lemma lem5329456 (p : nat) (n : nat) : (term66 p n) = (term67 p n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5329455 GEN_PVAR_229 p n)). Qed.
Lemma lem5329457 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5329458 (p : nat) (n : nat) : (term68 p n) = (term50 p n).
Proof. exact (MK_COMB (@lem5329457) (@lem5329456 p n)). Qed.
Lemma lem5329459 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329460 (x : nat) (p : nat) (n : nat) : (term54 x p n) = (term53 x p n).
Proof. exact (MK_COMB (@lem5329459 x) (@lem5329458 p n)). Qed.
Lemma lem5329461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329462 (x : nat) (p : nat) (n : nat) : (term69 x p n) = (term70 x p n).
Proof. exact (MK_COMB (@lem5329461) (@lem5329460 x p n)). Qed.
Lemma lem5329463 (p : nat) (x : nat) (n : nat) : (term55 p n x) = (term57 p x n).
Proof. exact (eq_refl (term55 p n x)). Qed.
Lemma lem5329464 (p : nat) (x : nat) (n : nat) : ((term54 x p n) = (term55 p n x)) = ((term53 x p n) = (term57 p x n)).
Proof. exact (MK_COMB (@lem5329462 x p n) (@lem5329463 p x n)). Qed.
Lemma lem5329465 (p : nat) (x : nat) (n : nat) : (term53 x p n) = (term57 p x n).
Proof. exact (EQ_MP (@lem5329464 p x n) (@lem5329447 p n x)). Qed.
Lemma lem5329468 (p : nat) (x : nat) (n : nat) : (term52 x p n) = (term57 p x n).
Proof. exact (TRANS (@lem5329443 x p n) (@lem5329465 p x n)). Qed.
Lemma lem5329469 (m : nat) (p : nat) (x : nat) (n : nat) : (term26 m x p n) = (term71 m p x n).
Proof. exact (MK_COMB (@lem5329432 m x p) (@lem5329468 p x n)). Qed.
Lemma lem5329472 (m : nat) (p : nat) (x : nat) (n : nat) : (term25 x m p n) = (term71 m p x n).
Proof. exact (TRANS (@lem5329392 m x p n) (@lem5329469 m p x n)). Qed.
Lemma lem5329473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329474 (m : nat) (p : nat) (x : nat) (n : nat) : (term72 x m p n) = (term73 m p x n).
Proof. exact (MK_COMB (@lem5329473) (@lem5329472 m p x n)). Qed.
Lemma lem5329476 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5329342 m n) (@lem5329341 m n)). Qed.
Lemma lem5329483 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329484 (x : nat) (m : nat) (n : nat) : (term28 x m n) = (term29 x m n).
Proof. exact (MK_COMB (@lem5329483 x) (@lem5329476 m n)). Qed.
Lemma lem5329486 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5329329 _83095 p x) (@lem5329328 _83095 p x)). Qed.
Lemma lem5329487 (p : nat -> Prop) (x : nat) : (term30 x p) = (p x).
Proof. exact (@lem5329486 nat p x). Qed.
Lemma lem5329488 (m : nat) (n : nat) (x : nat) : (term31 x m n) = (term32 m n x).
Proof. exact (@lem5329487 (term33 m n) x). Qed.
Lemma lem5329489 (m : nat) (x : nat) (n : nat) : (term32 m n x) = (term34 m x n).
Proof. exact (eq_refl (term32 m n x)). Qed.
Lemma lem5329490 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5329491 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (n : nat) : (term35 GEN_PVAR_229 m n x) = (term36 GEN_PVAR_229 m x n).
Proof. exact (MK_COMB (@lem5329490 GEN_PVAR_229) (@lem5329489 m x n)). Qed.
Lemma lem5329492 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5329493 (GEN_PVAR_229 : nat) (m : nat) (n : nat) (x : nat) : (term37 GEN_PVAR_229 m n x) = (term38 GEN_PVAR_229 m n x).
Proof. exact (MK_COMB (@lem5329491 GEN_PVAR_229 m x n) (@lem5329492 x)). Qed.
Lemma lem5329494 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term39 GEN_PVAR_229 m n) = (term40 GEN_PVAR_229 m n).
Proof. exact (fun_ext (fun x : nat => @lem5329493 GEN_PVAR_229 m n x)). Qed.
Lemma lem5329495 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5329496 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term41 GEN_PVAR_229 m n) = (term42 GEN_PVAR_229 m n).
Proof. exact (MK_COMB (@lem5329495) (@lem5329494 GEN_PVAR_229 m n)). Qed.
Lemma lem5329497 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5329496 GEN_PVAR_229 m n)). Qed.
Lemma lem5329498 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5329499 (m : nat) (n : nat) : (term45 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem5329498) (@lem5329497 m n)). Qed.
Lemma lem5329500 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329501 (x : nat) (m : nat) (n : nat) : (term31 x m n) = (term29 x m n).
Proof. exact (MK_COMB (@lem5329500 x) (@lem5329499 m n)). Qed.
Lemma lem5329502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329503 (x : nat) (m : nat) (n : nat) : (term46 x m n) = (term47 x m n).
Proof. exact (MK_COMB (@lem5329502) (@lem5329501 x m n)). Qed.
Lemma lem5329504 (m : nat) (x : nat) (n : nat) : (term32 m n x) = (term34 m x n).
Proof. exact (eq_refl (term32 m n x)). Qed.
Lemma lem5329505 (m : nat) (x : nat) (n : nat) : ((term31 x m n) = (term32 m n x)) = ((term29 x m n) = (term34 m x n)).
Proof. exact (MK_COMB (@lem5329503 x m n) (@lem5329504 m x n)). Qed.
Lemma lem5329506 (m : nat) (x : nat) (n : nat) : (term29 x m n) = (term34 m x n).
Proof. exact (EQ_MP (@lem5329505 m x n) (@lem5329488 m n x)). Qed.
Lemma lem5329509 (m : nat) (x : nat) (n : nat) : (term28 x m n) = (term34 m x n).
Proof. exact (TRANS (@lem5329484 x m n) (@lem5329506 m x n)). Qed.
Lemma lem5329510 (p : nat) (m : nat) (x : nat) (n : nat) : ((term25 x m p n) = (term28 x m n)) = ((term71 m p x n) = (term34 m x n)).
Proof. exact (MK_COMB (@lem5329474 m p x n) (@lem5329509 m x n)). Qed.
Lemma lem5329515 (p : nat) (m : nat) (n : nat) : (term74 p m n) = (term75 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329510 p m x n)). Qed.
Lemma lem5329516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329517 (p : nat) (m : nat) (n : nat) : (term22 p m n) = (term76 p m n).
Proof. exact (MK_COMB (@lem5329516) (@lem5329515 p m n)). Qed.
Lemma lem5329522 (p : nat) (m : nat) (n : nat) : ((term21 m p n) = (dotdot m n)) = (term76 p m n).
Proof. exact (TRANS (@lem5329380 p m n) (@lem5329517 p m n)). Qed.
Lemma lem5329523 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term77 m p n).
Proof. exact (eq_refl (term77 m p n)). Qed.
Lemma lem5329524 (p : nat) (m : nat) (n : nat) : (term78 p m n) = (term79 p m n).
Proof. exact (MK_COMB (@lem5329523 m p n) (@lem5329522 p m n)). Qed.
Lemma lem5329527 (p : nat) (m : nat) : (term80 p m) = (term81 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329524 p m n)). Qed.
Lemma lem5329528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329529 (p : nat) (m : nat) : (term82 p m) = (term83 p m).
Proof. exact (MK_COMB (@lem5329528) (@lem5329527 p m)). Qed.
Lemma lem5329534 (m : nat) : (term84 m) = (term85 m).
Proof. exact (fun_ext (fun p : nat => @lem5329529 p m)). Qed.
Lemma lem5329535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329536 (m : nat) : (term86 m) = (term87 m).
Proof. exact (MK_COMB (@lem5329535) (@lem5329534 m)). Qed.
Lemma lem5329541 : term88 = term89.
Proof. exact (fun_ext (fun m : nat => @lem5329536 m)). Qed.
Lemma lem5329542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329543 : term90 = term91.
Proof. exact (MK_COMB (@lem5329542) (@lem5329541)). Qed.
Lemma lem5329548 : term91 = term90.
Proof. exact (SYM (@lem5329543)). Qed.
Lemma lem5329600 (p : nat) (m : nat) (x : nat) (n : nat) : ((term71 m p x n) = (term34 m x n)) = ((term71 m p x n) = (term34 m x n)).
Proof. exact (eq_refl ((term71 m p x n) = (term34 m x n))). Qed.
Lemma lem5329601 (p : nat) (m : nat) (n : nat) : (term75 p m n) = (term75 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329600 p m x n)). Qed.
Lemma lem5329602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329603 (p : nat) (m : nat) (n : nat) : (term76 p m n) = (term76 p m n).
Proof. exact (MK_COMB (@lem5329602) (@lem5329601 p m n)). Qed.
Lemma lem5329610 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term77 m p n).
Proof. exact (eq_refl (term77 m p n)). Qed.
Lemma lem5329611 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term79 p m n).
Proof. exact (MK_COMB (@lem5329610 m p n) (@lem5329603 p m n)). Qed.
Lemma lem5329612 (p : nat) (m : nat) : (term81 p m) = (term81 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329611 p m n)). Qed.
Lemma lem5329613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329614 (p : nat) (m : nat) : (term83 p m) = (term83 p m).
Proof. exact (MK_COMB (@lem5329613) (@lem5329612 p m)). Qed.
Lemma lem5329615 (m : nat) : (term85 m) = (term85 m).
Proof. exact (fun_ext (fun p : nat => @lem5329614 p m)). Qed.
Lemma lem5329616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329617 (m : nat) : (term87 m) = (term87 m).
Proof. exact (MK_COMB (@lem5329616) (@lem5329615 m)). Qed.
Lemma lem5329618 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem5329617 m)). Qed.
Lemma lem5329619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329621 : term91 = term91.
Proof. exact (MK_COMB (@lem5329619) (@lem5329618)). Qed.
Lemma lem5329628 (m : nat) (p : nat) (n : nat) : (term92 m p n) = (term93 m p n).
Proof. exact (@lem17045 (term94 m p) (Peano.le p n)). Qed.
Lemma lem5329637 (m : nat) (x : nat) (p : nat) : (term95 m x p) = (term96 m x p).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x p)). Qed.
Lemma lem5329649 (p : nat) (x : nat) (n : nat) : (term97 p x n) = (term98 p x n).
Proof. exact (@lem17045 (term99 p x) (Peano.le x n)). Qed.
Lemma lem5329653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5329654 (m : nat) (x : nat) (p : nat) : (term100 m x p) = (term101 m x p).
Proof. exact (MK_COMB (@lem5329653) (@lem5329637 m x p)). Qed.
Lemma lem5329655 (m : nat) (p : nat) (x : nat) (n : nat) : (term102 m p x n) = (term103 m p x n).
Proof. exact (MK_COMB (@lem5329654 m x p) (@lem5329649 p x n)). Qed.
Lemma lem5329656 (m : nat) (p : nat) (x : nat) (n : nat) : (term104 m p x n) = (term102 m p x n).
Proof. exact (@lem17160 (term34 m x p) (term57 p x n)). Qed.
Lemma lem5329657 (m : nat) (p : nat) (x : nat) (n : nat) : (term104 m p x n) = (term103 m p x n).
Proof. exact (TRANS (@lem5329656 m p x n) (@lem5329655 m p x n)). Qed.
Lemma lem5329669 (m : nat) (x : nat) (n : nat) : (term95 m x n) = (term96 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5329672 (m : nat) (x : nat) (n : nat) : (term34 m x n) = (term34 m x n).
Proof. exact (eq_refl (term34 m x n)). Qed.
Lemma lem5329673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329674 (m : nat) (p : nat) (x : nat) (n : nat) : (term105 m p x n) = (term106 m p x n).
Proof. exact (MK_COMB (@lem5329673) (@lem5329657 m p x n)). Qed.
Lemma lem5329675 (p : nat) (m : nat) (x : nat) (n : nat) : (term107 p m x n) = (term108 p m x n).
Proof. exact (MK_COMB (@lem5329674 m p x n) (@lem5329672 m x n)). Qed.
Lemma lem5329677 (m : nat) (p : nat) (x : nat) (n : nat) : (term109 m p x n) = (term109 m p x n).
Proof. exact (eq_refl (term109 m p x n)). Qed.
Lemma lem5329678 (p : nat) (m : nat) (x : nat) (n : nat) : (term110 p m x n) = (term111 p m x n).
Proof. exact (MK_COMB (@lem5329677 m p x n) (@lem5329669 m x n)). Qed.
Lemma lem5329679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5329680 (p : nat) (m : nat) (x : nat) (n : nat) : (term112 p m x n) = (term113 p m x n).
Proof. exact (MK_COMB (@lem5329679) (@lem5329678 p m x n)). Qed.
Lemma lem5329681 (p : nat) (m : nat) (x : nat) (n : nat) : (term114 p m x n) = (term115 p m x n).
Proof. exact (MK_COMB (@lem5329680 p m x n) (@lem5329675 p m x n)). Qed.
Lemma lem5329682 (p : nat) (m : nat) (x : nat) (n : nat) : ((term71 m p x n) = (term34 m x n)) = (term114 p m x n).
Proof. exact (@lem17784 (term71 m p x n) (term34 m x n)). Qed.
Lemma lem5329683 (p : nat) (m : nat) (x : nat) (n : nat) : ((term71 m p x n) = (term34 m x n)) = (term115 p m x n).
Proof. exact (TRANS (@lem5329682 p m x n) (@lem5329681 p m x n)). Qed.
Lemma lem5329684 (p : nat) (m : nat) (n : nat) : (term75 p m n) = (term116 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329683 p m x n)). Qed.
Lemma lem5329685 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329686 (p : nat) (m : nat) (n : nat) : (term76 p m n) = (term117 p m n).
Proof. exact (MK_COMB (@lem5329685) (@lem5329684 p m n)). Qed.
Lemma lem5329687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329688 (m : nat) (p : nat) (n : nat) : (term118 m p n) = (term119 m p n).
Proof. exact (MK_COMB (@lem5329687) (@lem5329628 m p n)). Qed.
Lemma lem5329689 (p : nat) (m : nat) (n : nat) : (term120 p m n) = (term121 p m n).
Proof. exact (MK_COMB (@lem5329688 m p n) (@lem5329686 p m n)). Qed.
Lemma lem5329690 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term120 p m n).
Proof. exact (@lem17265 (term122 m p n) (term76 p m n)). Qed.
Lemma lem5329691 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term121 p m n).
Proof. exact (TRANS (@lem5329690 p m n) (@lem5329689 p m n)). Qed.
Lemma lem5329692 (p : nat) (m : nat) : (term81 p m) = (term123 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329691 p m n)). Qed.
Lemma lem5329693 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329694 (p : nat) (m : nat) : (term83 p m) = (term124 p m).
Proof. exact (MK_COMB (@lem5329693) (@lem5329692 p m)). Qed.
Lemma lem5329695 (m : nat) : (term85 m) = (term125 m).
Proof. exact (fun_ext (fun p : nat => @lem5329694 p m)). Qed.
Lemma lem5329696 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329697 (m : nat) : (term87 m) = (term126 m).
Proof. exact (MK_COMB (@lem5329696) (@lem5329695 m)). Qed.
Lemma lem5329698 : term89 = term127.
Proof. exact (fun_ext (fun m : nat => @lem5329697 m)). Qed.
Lemma lem5329699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329700 : term91 = term128.
Proof. exact (MK_COMB (@lem5329699) (@lem5329698)). Qed.
Lemma lem5329701 : term91 = term128.
Proof. exact (TRANS (@lem5329621) (@lem5329700)). Qed.
Lemma lem5329702 (p : nat) (m : nat) (x : nat) (n : nat) : (term115 p m x n) = (term115 p m x n).
Proof. exact (eq_refl (term115 p m x n)). Qed.
Lemma lem5329703 (p : nat) (m : nat) (n : nat) : (term116 p m n) = (term116 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329702 p m x n)). Qed.
Lemma lem5329704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329705 (p : nat) (m : nat) (n : nat) : (term117 p m n) = (term117 p m n).
Proof. exact (MK_COMB (@lem5329704) (@lem5329703 p m n)). Qed.
Lemma lem5329708 (m : nat) (p : nat) (n : nat) : (term119 m p n) = (term119 m p n).
Proof. exact (eq_refl (term119 m p n)). Qed.
Lemma lem5329709 (p : nat) (m : nat) (n : nat) : (term121 p m n) = (term121 p m n).
Proof. exact (MK_COMB (@lem5329708 m p n) (@lem5329705 p m n)). Qed.
Lemma lem5329710 (p : nat) (m : nat) : (term123 p m) = (term123 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329709 p m n)). Qed.
Lemma lem5329711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329712 (p : nat) (m : nat) : (term124 p m) = (term124 p m).
Proof. exact (MK_COMB (@lem5329711) (@lem5329710 p m)). Qed.
Lemma lem5329713 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun p : nat => @lem5329712 p m)). Qed.
Lemma lem5329714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329715 (m : nat) : (term126 m) = (term126 m).
Proof. exact (MK_COMB (@lem5329714) (@lem5329713 m)). Qed.
Lemma lem5329716 : term127 = term127.
Proof. exact (fun_ext (fun m : nat => @lem5329715 m)). Qed.
Lemma lem5329717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329718 : term128 = term128.
Proof. exact (MK_COMB (@lem5329717) (@lem5329716)). Qed.
Lemma lem5329767 : term91 = term128.
Proof. exact (TRANS (@lem5329701) (@lem5329718)). Qed.
Lemma lem5329884 (p : nat) (m : nat) (x : nat) (n : nat) : (term115 p m x n) = (term115 p m x n).
Proof. exact (eq_refl (term115 p m x n)). Qed.
Lemma lem5329885 (p : nat) (m : nat) (n : nat) : (term116 p m n) = (term116 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329884 p m x n)). Qed.
Lemma lem5329886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329887 (p : nat) (m : nat) (n : nat) : (term117 p m n) = (term117 p m n).
Proof. exact (MK_COMB (@lem5329886) (@lem5329885 p m n)). Qed.
Lemma lem5329912 (m : nat) (p : nat) (n : nat) : (term119 m p n) = (term119 m p n).
Proof. exact (eq_refl (term119 m p n)). Qed.
Lemma lem5329913 (p : nat) (m : nat) (n : nat) : (term121 p m n) = (term121 p m n).
Proof. exact (MK_COMB (@lem5329912 m p n) (@lem5329887 p m n)). Qed.
Lemma lem5329914 (p : nat) (m : nat) : (term123 p m) = (term123 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329913 p m n)). Qed.
Lemma lem5329915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329916 (p : nat) (m : nat) : (term124 p m) = (term124 p m).
Proof. exact (MK_COMB (@lem5329915) (@lem5329914 p m)). Qed.
Lemma lem5329917 (m : nat) : (term125 m) = (term125 m).
Proof. exact (fun_ext (fun p : nat => @lem5329916 p m)). Qed.
Lemma lem5329918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329919 (m : nat) : (term126 m) = (term126 m).
Proof. exact (MK_COMB (@lem5329918) (@lem5329917 m)). Qed.
Lemma lem5329920 : term127 = term127.
Proof. exact (fun_ext (fun m : nat => @lem5329919 m)). Qed.
Lemma lem5329921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329922 : term128 = term128.
Proof. exact (MK_COMB (@lem5329921) (@lem5329920)). Qed.
Lemma lem5329923 : term91 = term128.
Proof. exact (TRANS (@lem5329767) (@lem5329922)). Qed.
Lemma lem5329925 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5329926 (P : Prop) (Q : nat -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem5329925 nat P Q). Qed.
Lemma lem5329927 (p : nat) (m : nat) (n : nat) : (term133 p m n) = (term134 p m n).
Proof. exact (@lem5329926 (term93 m p n) (term116 p m n)). Qed.
Lemma lem5329928 (p : nat) (m : nat) (x : nat) (n : nat) : (term135 p m n x) = (term115 p m x n).
Proof. exact (eq_refl (term135 p m n x)). Qed.
Lemma lem5329929 (p : nat) (m : nat) (n : nat) : (term136 p m n) = (term116 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329928 p m x n)). Qed.
Lemma lem5329930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329931 (p : nat) (m : nat) (n : nat) : (term137 p m n) = (term117 p m n).
Proof. exact (MK_COMB (@lem5329930) (@lem5329929 p m n)). Qed.
Lemma lem5329932 (m : nat) (p : nat) (n : nat) : (term119 m p n) = (term119 m p n).
Proof. exact (eq_refl (term119 m p n)). Qed.
Lemma lem5329933 (p : nat) (m : nat) (n : nat) : (term133 p m n) = (term121 p m n).
Proof. exact (MK_COMB (@lem5329932 m p n) (@lem5329931 p m n)). Qed.
Lemma lem5329934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329935 (p : nat) (m : nat) (n : nat) : (term138 p m n) = (term139 p m n).
Proof. exact (MK_COMB (@lem5329934) (@lem5329933 p m n)). Qed.
Lemma lem5329936 (p : nat) (m : nat) (x : nat) (n : nat) : (term135 p m n x) = (term115 p m x n).
Proof. exact (eq_refl (term135 p m n x)). Qed.
Lemma lem5329937 (m : nat) (p : nat) (n : nat) : (term119 m p n) = (term119 m p n).
Proof. exact (eq_refl (term119 m p n)). Qed.
Lemma lem5329938 (p : nat) (m : nat) (x : nat) (n : nat) : (term140 p m n x) = (term141 p m x n).
Proof. exact (MK_COMB (@lem5329937 m p n) (@lem5329936 p m x n)). Qed.
Lemma lem5329939 (p : nat) (m : nat) (n : nat) : (term142 p m n) = (term143 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5329938 p m x n)). Qed.
Lemma lem5329940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329941 (p : nat) (m : nat) (n : nat) : (term134 p m n) = (term144 p m n).
Proof. exact (MK_COMB (@lem5329940) (@lem5329939 p m n)). Qed.
Lemma lem5329942 (p : nat) (m : nat) (n : nat) : ((term133 p m n) = (term134 p m n)) = ((term121 p m n) = (term144 p m n)).
Proof. exact (MK_COMB (@lem5329935 p m n) (@lem5329941 p m n)). Qed.
Lemma lem5329943 (p : nat) (m : nat) (n : nat) : (term121 p m n) = (term144 p m n).
Proof. exact (EQ_MP (@lem5329942 p m n) (@lem5329927 p m n)). Qed.
Lemma lem5329944 (p : nat) (m : nat) : (term123 p m) = (term145 p m).
Proof. exact (fun_ext (fun n : nat => @lem5329943 p m n)). Qed.
Lemma lem5329945 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329946 (p : nat) (m : nat) : (term124 p m) = (term146 p m).
Proof. exact (MK_COMB (@lem5329945) (@lem5329944 p m)). Qed.
Lemma lem5329947 (m : nat) : (term125 m) = (term147 m).
Proof. exact (fun_ext (fun p : nat => @lem5329946 p m)). Qed.
Lemma lem5329948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329949 (m : nat) : (term126 m) = (term148 m).
Proof. exact (MK_COMB (@lem5329948) (@lem5329947 m)). Qed.
Lemma lem5329950 : term127 = term149.
Proof. exact (fun_ext (fun m : nat => @lem5329949 m)). Qed.
Lemma lem5329951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329952 : term128 = term150.
Proof. exact (MK_COMB (@lem5329951) (@lem5329950)). Qed.
Lemma lem5329953 : term91 = term150.
Proof. exact (TRANS (@lem5329923) (@lem5329952)). Qed.
Lemma lem5329955 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5329956 (m : nat) (p : nat) : (term94 m p) = (term152 m p).
Proof. exact (@lem5329955 m (term51 p)). Qed.
Lemma lem5329958 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5329959 (p : nat) : (term155 p) = (term156 p).
Proof. exact (@lem5329958 p term157). Qed.
Lemma lem5329960 (m : nat) : (term158 m) = (term158 m).
Proof. exact (eq_refl (term158 m)). Qed.
Lemma lem5329961 (m : nat) (p : nat) : (term152 m p) = (term159 m p).
Proof. exact (MK_COMB (@lem5329960 m) (@lem5329959 p)). Qed.
Lemma lem5329962 (m : nat) (p : nat) : (term94 m p) = (term159 m p).
Proof. exact (TRANS (@lem5329956 m p) (@lem5329961 m p)). Qed.
Lemma lem5329963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5329964 (m : nat) (p : nat) : (term160 m p) = (term161 m p).
Proof. exact (MK_COMB (@lem5329963) (@lem5329962 m p)). Qed.
Lemma lem5329965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329966 (m : nat) (p : nat) : (term162 m p) = (term163 m p).
Proof. exact (MK_COMB (@lem5329965) (@lem5329964 m p)). Qed.
Lemma lem5329968 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5329969 (p : nat) (n : nat) : (Peano.le p n) = (term151 p n).
Proof. exact (@lem5329968 p n). Qed.
Lemma lem5329970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5329971 (p : nat) (n : nat) : (term164 p n) = (term165 p n).
Proof. exact (MK_COMB (@lem5329970) (@lem5329969 p n)). Qed.
Lemma lem5329972 (m : nat) (p : nat) (n : nat) : (term93 m p n) = (term166 m p n).
Proof. exact (MK_COMB (@lem5329966 m p) (@lem5329971 p n)). Qed.
Lemma lem5329973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329974 (m : nat) (p : nat) (n : nat) : (term119 m p n) = (term167 m p n).
Proof. exact (MK_COMB (@lem5329973) (@lem5329972 m p n)). Qed.
Lemma lem5329976 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5329977 (m : nat) (x : nat) : (Peano.le m x) = (term151 m x).
Proof. exact (@lem5329976 m x). Qed.
Lemma lem5329978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5329979 (m : nat) (x : nat) : (term168 m x) = (term169 m x).
Proof. exact (MK_COMB (@lem5329978) (@lem5329977 m x)). Qed.
Lemma lem5329981 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5329982 (x : nat) (p : nat) : (Peano.le x p) = (term151 x p).
Proof. exact (@lem5329981 x p). Qed.
Lemma lem5329983 (m : nat) (x : nat) (p : nat) : (term34 m x p) = (term170 m x p).
Proof. exact (MK_COMB (@lem5329979 m x) (@lem5329982 x p)). Qed.
Lemma lem5329984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5329985 (m : nat) (x : nat) (p : nat) : (term49 m x p) = (term171 m x p).
Proof. exact (MK_COMB (@lem5329984) (@lem5329983 m x p)). Qed.
Lemma lem5329987 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5329988 (p : nat) (x : nat) : (term99 p x) = (term172 p x).
Proof. exact (@lem5329987 (term51 p) x). Qed.
Lemma lem5329990 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5329991 (p : nat) : (term155 p) = (term156 p).
Proof. exact (@lem5329990 p term157). Qed.
Lemma lem5329992 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5329993 (p : nat) : (term173 p) = (term174 p).
Proof. exact (MK_COMB (@lem5329992) (@lem5329991 p)). Qed.
Lemma lem5329994 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5329995 (p : nat) (x : nat) : (term172 p x) = (term175 p x).
Proof. exact (MK_COMB (@lem5329993 p) (@lem5329994 x)). Qed.
Lemma lem5329996 (p : nat) (x : nat) : (term99 p x) = (term175 p x).
Proof. exact (TRANS (@lem5329988 p x) (@lem5329995 p x)). Qed.
Lemma lem5329997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5329998 (p : nat) (x : nat) : (term176 p x) = (term177 p x).
Proof. exact (MK_COMB (@lem5329997) (@lem5329996 p x)). Qed.
Lemma lem5330000 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330001 (x : nat) (n : nat) : (Peano.le x n) = (term151 x n).
Proof. exact (@lem5330000 x n). Qed.
Lemma lem5330002 (p : nat) (x : nat) (n : nat) : (term57 p x n) = (term178 p x n).
Proof. exact (MK_COMB (@lem5329998 p x) (@lem5330001 x n)). Qed.
Lemma lem5330003 (m : nat) (p : nat) (x : nat) (n : nat) : (term71 m p x n) = (term179 m p x n).
Proof. exact (MK_COMB (@lem5329985 m x p) (@lem5330002 p x n)). Qed.
Lemma lem5330004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330005 (m : nat) (p : nat) (x : nat) (n : nat) : (term109 m p x n) = (term180 m p x n).
Proof. exact (MK_COMB (@lem5330004) (@lem5330003 m p x n)). Qed.
Lemma lem5330007 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330008 (m : nat) (x : nat) : (Peano.le m x) = (term151 m x).
Proof. exact (@lem5330007 m x). Qed.
Lemma lem5330009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330010 (m : nat) (x : nat) : (term164 m x) = (term165 m x).
Proof. exact (MK_COMB (@lem5330009) (@lem5330008 m x)). Qed.
Lemma lem5330011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330012 (m : nat) (x : nat) : (term181 m x) = (term182 m x).
Proof. exact (MK_COMB (@lem5330011) (@lem5330010 m x)). Qed.
Lemma lem5330014 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330015 (x : nat) (n : nat) : (Peano.le x n) = (term151 x n).
Proof. exact (@lem5330014 x n). Qed.
Lemma lem5330016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330017 (x : nat) (n : nat) : (term164 x n) = (term165 x n).
Proof. exact (MK_COMB (@lem5330016) (@lem5330015 x n)). Qed.
Lemma lem5330018 (m : nat) (x : nat) (n : nat) : (term96 m x n) = (term183 m x n).
Proof. exact (MK_COMB (@lem5330012 m x) (@lem5330017 x n)). Qed.
Lemma lem5330019 (p : nat) (m : nat) (x : nat) (n : nat) : (term111 p m x n) = (term184 p m x n).
Proof. exact (MK_COMB (@lem5330005 m p x n) (@lem5330018 m x n)). Qed.
Lemma lem5330020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330021 (p : nat) (m : nat) (x : nat) (n : nat) : (term113 p m x n) = (term185 p m x n).
Proof. exact (MK_COMB (@lem5330020) (@lem5330019 p m x n)). Qed.
Lemma lem5330023 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330024 (m : nat) (x : nat) : (Peano.le m x) = (term151 m x).
Proof. exact (@lem5330023 m x). Qed.
Lemma lem5330025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330026 (m : nat) (x : nat) : (term164 m x) = (term165 m x).
Proof. exact (MK_COMB (@lem5330025) (@lem5330024 m x)). Qed.
Lemma lem5330027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330028 (m : nat) (x : nat) : (term181 m x) = (term182 m x).
Proof. exact (MK_COMB (@lem5330027) (@lem5330026 m x)). Qed.
Lemma lem5330030 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330031 (x : nat) (p : nat) : (Peano.le x p) = (term151 x p).
Proof. exact (@lem5330030 x p). Qed.
Lemma lem5330032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330033 (x : nat) (p : nat) : (term164 x p) = (term165 x p).
Proof. exact (MK_COMB (@lem5330032) (@lem5330031 x p)). Qed.
Lemma lem5330034 (m : nat) (x : nat) (p : nat) : (term96 m x p) = (term183 m x p).
Proof. exact (MK_COMB (@lem5330028 m x) (@lem5330033 x p)). Qed.
Lemma lem5330035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330036 (m : nat) (x : nat) (p : nat) : (term101 m x p) = (term186 m x p).
Proof. exact (MK_COMB (@lem5330035) (@lem5330034 m x p)). Qed.
Lemma lem5330038 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330039 (p : nat) (x : nat) : (term99 p x) = (term172 p x).
Proof. exact (@lem5330038 (term51 p) x). Qed.
Lemma lem5330041 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5330042 (p : nat) : (term155 p) = (term156 p).
Proof. exact (@lem5330041 p term157). Qed.
Lemma lem5330043 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5330044 (p : nat) : (term173 p) = (term174 p).
Proof. exact (MK_COMB (@lem5330043) (@lem5330042 p)). Qed.
Lemma lem5330045 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5330046 (p : nat) (x : nat) : (term172 p x) = (term175 p x).
Proof. exact (MK_COMB (@lem5330044 p) (@lem5330045 x)). Qed.
Lemma lem5330047 (p : nat) (x : nat) : (term99 p x) = (term175 p x).
Proof. exact (TRANS (@lem5330039 p x) (@lem5330046 p x)). Qed.
Lemma lem5330048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330049 (p : nat) (x : nat) : (term187 p x) = (term188 p x).
Proof. exact (MK_COMB (@lem5330048) (@lem5330047 p x)). Qed.
Lemma lem5330050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330051 (p : nat) (x : nat) : (term189 p x) = (term190 p x).
Proof. exact (MK_COMB (@lem5330050) (@lem5330049 p x)). Qed.
Lemma lem5330053 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330054 (x : nat) (n : nat) : (Peano.le x n) = (term151 x n).
Proof. exact (@lem5330053 x n). Qed.
Lemma lem5330055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5330056 (x : nat) (n : nat) : (term164 x n) = (term165 x n).
Proof. exact (MK_COMB (@lem5330055) (@lem5330054 x n)). Qed.
Lemma lem5330057 (p : nat) (x : nat) (n : nat) : (term98 p x n) = (term191 p x n).
Proof. exact (MK_COMB (@lem5330051 p x) (@lem5330056 x n)). Qed.
Lemma lem5330058 (m : nat) (p : nat) (x : nat) (n : nat) : (term103 m p x n) = (term192 m p x n).
Proof. exact (MK_COMB (@lem5330036 m x p) (@lem5330057 p x n)). Qed.
Lemma lem5330059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330060 (m : nat) (p : nat) (x : nat) (n : nat) : (term106 m p x n) = (term193 m p x n).
Proof. exact (MK_COMB (@lem5330059) (@lem5330058 m p x n)). Qed.
Lemma lem5330062 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330063 (m : nat) (x : nat) : (Peano.le m x) = (term151 m x).
Proof. exact (@lem5330062 m x). Qed.
Lemma lem5330064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330065 (m : nat) (x : nat) : (term168 m x) = (term169 m x).
Proof. exact (MK_COMB (@lem5330064) (@lem5330063 m x)). Qed.
Lemma lem5330067 (m : nat) (n : nat) : (Peano.le m n) = (term151 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5330068 (x : nat) (n : nat) : (Peano.le x n) = (term151 x n).
Proof. exact (@lem5330067 x n). Qed.
Lemma lem5330069 (m : nat) (x : nat) (n : nat) : (term34 m x n) = (term170 m x n).
Proof. exact (MK_COMB (@lem5330065 m x) (@lem5330068 x n)). Qed.
Lemma lem5330070 (p : nat) (m : nat) (x : nat) (n : nat) : (term108 p m x n) = (term194 p m x n).
Proof. exact (MK_COMB (@lem5330060 m p x n) (@lem5330069 m x n)). Qed.
Lemma lem5330071 (p : nat) (m : nat) (x : nat) (n : nat) : (term115 p m x n) = (term195 p m x n).
Proof. exact (MK_COMB (@lem5330021 p m x n) (@lem5330070 p m x n)). Qed.
Lemma lem5330072 (p : nat) (m : nat) (x : nat) (n : nat) : (term141 p m x n) = (term196 p m x n).
Proof. exact (MK_COMB (@lem5329974 m p n) (@lem5330071 p m x n)). Qed.
Lemma lem5330073 (p : nat) (m : nat) (n : nat) : (term143 p m n) = (term197 p m n).
Proof. exact (fun_ext (fun x : nat => @lem5330072 p m x n)). Qed.
Lemma lem5330074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5330075 (p : nat) (m : nat) (n : nat) : (term144 p m n) = (term198 p m n).
Proof. exact (MK_COMB (@lem5330074) (@lem5330073 p m n)). Qed.
Lemma lem5330076 (p : nat) (m : nat) : (term145 p m) = (term199 p m).
Proof. exact (fun_ext (fun n : nat => @lem5330075 p m n)). Qed.
Lemma lem5330077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5330078 (p : nat) (m : nat) : (term146 p m) = (term200 p m).
Proof. exact (MK_COMB (@lem5330077) (@lem5330076 p m)). Qed.
Lemma lem5330079 (m : nat) : (term147 m) = (term201 m).
Proof. exact (fun_ext (fun p : nat => @lem5330078 p m)). Qed.
Lemma lem5330080 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5330081 (m : nat) : (term148 m) = (term202 m).
Proof. exact (MK_COMB (@lem5330080) (@lem5330079 m)). Qed.
Lemma lem5330082 : term149 = term203.
Proof. exact (fun_ext (fun m : nat => @lem5330081 m)). Qed.
Lemma lem5330083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5330084 : term150 = term204.
Proof. exact (MK_COMB (@lem5330083) (@lem5330082)). Qed.
Lemma lem5330085 : term91 = term204.
Proof. exact (TRANS (@lem5329953) (@lem5330084)). Qed.
Lemma lem5330086 (m : nat) : term205 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5330087 (m : nat) : (term205 m) = (term206 m).
Proof. exact (eq_refl (term205 m)). Qed.
Lemma lem5330088 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem5330087 m) (@lem5330086 m)). Qed.
Lemma lem5330089 (n : nat) : term205 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5330090 (n : nat) : (term205 n) = (term206 n).
Proof. exact (eq_refl (term205 n)). Qed.
Lemma lem5330091 (n : nat) : term206 n.
Proof. exact (EQ_MP (@lem5330090 n) (@lem5330089 n)). Qed.
Lemma lem5330092 (p : nat) : term205 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem5330093 (p : nat) : (term205 p) = (term206 p).
Proof. exact (eq_refl (term205 p)). Qed.
Lemma lem5330094 (p : nat) : term206 p.
Proof. exact (EQ_MP (@lem5330093 p) (@lem5330092 p)). Qed.
Lemma lem5330095 (x : nat) : term205 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5330096 (x : nat) : (term205 x) = (term206 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem5330097 (x : nat) : term206 x.
Proof. exact (EQ_MP (@lem5330096 x) (@lem5330095 x)). Qed.
Lemma lem5330098 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term207 _69706 _69704 _69707 _69705) = (term208 _69706 _69704 _69707 _69705).
Proof. exact (@lem2318604 (term208 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330144 (_69704 : int) (_69706 : int) : (term209 _69704 _69706) = (term210 _69704 _69706).
Proof. exact (@lem16933 (term210 _69704 _69706)). Qed.
Lemma lem5330147 (_69706 : int) (_69705 : int) : (term211 _69706 _69705) = (int_le _69706 _69705).
Proof. exact (@lem16933 (int_le _69706 _69705)). Qed.
Lemma lem5330148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330149 (_69704 : int) (_69706 : int) : (term212 _69704 _69706) = (term213 _69704 _69706).
Proof. exact (MK_COMB (@lem5330148) (@lem5330144 _69704 _69706)). Qed.
Lemma lem5330150 (_69704 : int) (_69706 : int) (_69705 : int) : (term214 _69704 _69706 _69705) = (term215 _69704 _69706 _69705).
Proof. exact (MK_COMB (@lem5330149 _69704 _69706) (@lem5330147 _69706 _69705)). Qed.
Lemma lem5330151 (_69704 : int) (_69706 : int) (_69705 : int) : (term216 _69704 _69706 _69705) = (term214 _69704 _69706 _69705).
Proof. exact (@lem17160 (term217 _69704 _69706) (term218 _69706 _69705)). Qed.
Lemma lem5330152 (_69704 : int) (_69706 : int) (_69705 : int) : (term216 _69704 _69706 _69705) = (term215 _69704 _69706 _69705).
Proof. exact (TRANS (@lem5330151 _69704 _69706 _69705) (@lem5330150 _69704 _69706 _69705)). Qed.
Lemma lem5330159 (_69704 : int) (_69707 : int) (_69706 : int) : (term219 _69704 _69707 _69706) = (term220 _69704 _69707 _69706).
Proof. exact (@lem17045 (int_le _69704 _69707) (int_le _69707 _69706)). Qed.
Lemma lem5330166 (_69706 : int) (_69707 : int) (_69705 : int) : (term221 _69706 _69707 _69705) = (term222 _69706 _69707 _69705).
Proof. exact (@lem17045 (term223 _69706 _69707) (int_le _69707 _69705)). Qed.
Lemma lem5330167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330168 (_69704 : int) (_69707 : int) (_69706 : int) : (term224 _69704 _69707 _69706) = (term225 _69704 _69707 _69706).
Proof. exact (MK_COMB (@lem5330167) (@lem5330159 _69704 _69707 _69706)). Qed.
Lemma lem5330169 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term226 _69704 _69706 _69707 _69705) = (term227 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330168 _69704 _69707 _69706) (@lem5330166 _69706 _69707 _69705)). Qed.
Lemma lem5330170 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term228 _69704 _69706 _69707 _69705) = (term226 _69704 _69706 _69707 _69705).
Proof. exact (@lem17160 (term229 _69704 _69707 _69706) (term230 _69706 _69707 _69705)). Qed.
Lemma lem5330171 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term228 _69704 _69706 _69707 _69705) = (term227 _69704 _69706 _69707 _69705).
Proof. exact (TRANS (@lem5330170 _69704 _69706 _69707 _69705) (@lem5330169 _69704 _69706 _69707 _69705)). Qed.
Lemma lem5330174 (_69704 : int) (_69707 : int) : (term211 _69704 _69707) = (int_le _69704 _69707).
Proof. exact (@lem16933 (int_le _69704 _69707)). Qed.
Lemma lem5330177 (_69707 : int) (_69705 : int) : (term211 _69707 _69705) = (int_le _69707 _69705).
Proof. exact (@lem16933 (int_le _69707 _69705)). Qed.
Lemma lem5330178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330179 (_69704 : int) (_69707 : int) : (term231 _69704 _69707) = (term232 _69704 _69707).
Proof. exact (MK_COMB (@lem5330178) (@lem5330174 _69704 _69707)). Qed.
Lemma lem5330180 (_69704 : int) (_69707 : int) (_69705 : int) : (term233 _69704 _69707 _69705) = (term229 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330179 _69704 _69707) (@lem5330177 _69707 _69705)). Qed.
Lemma lem5330181 (_69704 : int) (_69707 : int) (_69705 : int) : (term234 _69704 _69707 _69705) = (term233 _69704 _69707 _69705).
Proof. exact (@lem17160 (term218 _69704 _69707) (term218 _69707 _69705)). Qed.
Lemma lem5330182 (_69704 : int) (_69707 : int) (_69705 : int) : (term234 _69704 _69707 _69705) = (term229 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330181 _69704 _69707 _69705) (@lem5330180 _69704 _69707 _69705)). Qed.
Lemma lem5330183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330184 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term235 _69704 _69706 _69707 _69705) = (term236 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330183) (@lem5330171 _69704 _69706 _69707 _69705)). Qed.
Lemma lem5330185 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term237 _69706 _69704 _69707 _69705) = (term238 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330184 _69704 _69706 _69707 _69705) (@lem5330182 _69704 _69707 _69705)). Qed.
Lemma lem5330186 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term239 _69706 _69704 _69707 _69705) = (term237 _69706 _69704 _69707 _69705).
Proof. exact (@lem17160 (term240 _69704 _69706 _69707 _69705) (term220 _69704 _69707 _69705)). Qed.
Lemma lem5330187 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term239 _69706 _69704 _69707 _69705) = (term238 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330186 _69706 _69704 _69707 _69705) (@lem5330185 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330190 (_69704 : int) (_69707 : int) : (term211 _69704 _69707) = (int_le _69704 _69707).
Proof. exact (@lem16933 (int_le _69704 _69707)). Qed.
Lemma lem5330193 (_69707 : int) (_69706 : int) : (term211 _69707 _69706) = (int_le _69707 _69706).
Proof. exact (@lem16933 (int_le _69707 _69706)). Qed.
Lemma lem5330194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330195 (_69704 : int) (_69707 : int) : (term231 _69704 _69707) = (term232 _69704 _69707).
Proof. exact (MK_COMB (@lem5330194) (@lem5330190 _69704 _69707)). Qed.
Lemma lem5330196 (_69704 : int) (_69707 : int) (_69706 : int) : (term233 _69704 _69707 _69706) = (term229 _69704 _69707 _69706).
Proof. exact (MK_COMB (@lem5330195 _69704 _69707) (@lem5330193 _69707 _69706)). Qed.
Lemma lem5330197 (_69704 : int) (_69707 : int) (_69706 : int) : (term234 _69704 _69707 _69706) = (term233 _69704 _69707 _69706).
Proof. exact (@lem17160 (term218 _69704 _69707) (term218 _69707 _69706)). Qed.
Lemma lem5330198 (_69704 : int) (_69707 : int) (_69706 : int) : (term234 _69704 _69707 _69706) = (term229 _69704 _69707 _69706).
Proof. exact (TRANS (@lem5330197 _69704 _69707 _69706) (@lem5330196 _69704 _69707 _69706)). Qed.
Lemma lem5330201 (_69706 : int) (_69707 : int) : (term241 _69706 _69707) = (term223 _69706 _69707).
Proof. exact (@lem16933 (term223 _69706 _69707)). Qed.
Lemma lem5330204 (_69707 : int) (_69705 : int) : (term211 _69707 _69705) = (int_le _69707 _69705).
Proof. exact (@lem16933 (int_le _69707 _69705)). Qed.
Lemma lem5330205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330206 (_69706 : int) (_69707 : int) : (term242 _69706 _69707) = (term243 _69706 _69707).
Proof. exact (MK_COMB (@lem5330205) (@lem5330201 _69706 _69707)). Qed.
Lemma lem5330207 (_69706 : int) (_69707 : int) (_69705 : int) : (term244 _69706 _69707 _69705) = (term230 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330206 _69706 _69707) (@lem5330204 _69707 _69705)). Qed.
Lemma lem5330208 (_69706 : int) (_69707 : int) (_69705 : int) : (term245 _69706 _69707 _69705) = (term244 _69706 _69707 _69705).
Proof. exact (@lem17160 (term246 _69706 _69707) (term218 _69707 _69705)). Qed.
Lemma lem5330209 (_69706 : int) (_69707 : int) (_69705 : int) : (term245 _69706 _69707 _69705) = (term230 _69706 _69707 _69705).
Proof. exact (TRANS (@lem5330208 _69706 _69707 _69705) (@lem5330207 _69706 _69707 _69705)). Qed.
Lemma lem5330210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330211 (_69704 : int) (_69707 : int) (_69706 : int) : (term247 _69704 _69707 _69706) = (term248 _69704 _69707 _69706).
Proof. exact (MK_COMB (@lem5330210) (@lem5330198 _69704 _69707 _69706)). Qed.
Lemma lem5330212 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term249 _69704 _69706 _69707 _69705) = (term240 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330211 _69704 _69707 _69706) (@lem5330209 _69706 _69707 _69705)). Qed.
Lemma lem5330213 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term250 _69704 _69706 _69707 _69705) = (term249 _69704 _69706 _69707 _69705).
Proof. exact (@lem17045 (term220 _69704 _69707 _69706) (term222 _69706 _69707 _69705)). Qed.
Lemma lem5330214 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term250 _69704 _69706 _69707 _69705) = (term240 _69704 _69706 _69707 _69705).
Proof. exact (TRANS (@lem5330213 _69704 _69706 _69707 _69705) (@lem5330212 _69704 _69706 _69707 _69705)). Qed.
Lemma lem5330221 (_69704 : int) (_69707 : int) (_69705 : int) : (term219 _69704 _69707 _69705) = (term220 _69704 _69707 _69705).
Proof. exact (@lem17045 (int_le _69704 _69707) (int_le _69707 _69705)). Qed.
Lemma lem5330222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330223 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term251 _69704 _69706 _69707 _69705) = (term252 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330222) (@lem5330214 _69704 _69706 _69707 _69705)). Qed.
Lemma lem5330224 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term253 _69706 _69704 _69707 _69705) = (term254 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330223 _69704 _69706 _69707 _69705) (@lem5330221 _69704 _69707 _69705)). Qed.
Lemma lem5330225 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term255 _69706 _69704 _69707 _69705) = (term253 _69706 _69704 _69707 _69705).
Proof. exact (@lem17160 (term227 _69704 _69706 _69707 _69705) (term229 _69704 _69707 _69705)). Qed.
Lemma lem5330226 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term255 _69706 _69704 _69707 _69705) = (term254 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330225 _69706 _69704 _69707 _69705) (@lem5330224 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330228 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term256 _69706 _69704 _69707 _69705) = (term257 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330227) (@lem5330187 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330229 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term258 _69706 _69704 _69707 _69705) = (term259 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330228 _69706 _69704 _69707 _69705) (@lem5330226 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330230 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term260 _69706 _69704 _69707 _69705) = (term258 _69706 _69704 _69707 _69705).
Proof. exact (@lem17045 (term261 _69706 _69704 _69707 _69705) (term262 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330231 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term260 _69706 _69704 _69707 _69705) = (term259 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330230 _69706 _69704 _69707 _69705) (@lem5330229 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330233 (_69704 : int) (_69706 : int) (_69705 : int) : (term263 _69704 _69706 _69705) = (term264 _69704 _69706 _69705).
Proof. exact (MK_COMB (@lem5330232) (@lem5330152 _69704 _69706 _69705)). Qed.
Lemma lem5330234 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term265 _69706 _69704 _69707 _69705) = (term266 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330233 _69704 _69706 _69705) (@lem5330231 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330235 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term267 _69706 _69704 _69707 _69705) = (term265 _69706 _69704 _69707 _69705).
Proof. exact (@lem17160 (term268 _69704 _69706 _69705) (term269 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330236 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term267 _69706 _69704 _69707 _69705) = (term266 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330235 _69706 _69704 _69707 _69705) (@lem5330234 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330238 (_69707 : int) : (term270 _69707) = (term270 _69707).
Proof. exact (eq_refl (term270 _69707)). Qed.
Lemma lem5330239 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term271 _69706 _69704 _69707 _69705) = (term272 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330238 _69707) (@lem5330236 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330240 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term273 _69706 _69704 _69707 _69705) = (term271 _69706 _69704 _69707 _69705).
Proof. exact (@lem17362 (term274 _69707) (term275 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330241 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term273 _69706 _69704 _69707 _69705) = (term272 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330240 _69706 _69704 _69707 _69705) (@lem5330239 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330243 (_69706 : int) : (term270 _69706) = (term270 _69706).
Proof. exact (eq_refl (term270 _69706)). Qed.
Lemma lem5330244 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term276 _69706 _69704 _69707 _69705) = (term277 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330243 _69706) (@lem5330241 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330245 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term278 _69706 _69704 _69707 _69705) = (term276 _69706 _69704 _69707 _69705).
Proof. exact (@lem17362 (term274 _69706) (term279 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330246 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term278 _69706 _69704 _69707 _69705) = (term277 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330245 _69706 _69704 _69707 _69705) (@lem5330244 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330248 (_69705 : int) : (term270 _69705) = (term270 _69705).
Proof. exact (eq_refl (term270 _69705)). Qed.
Lemma lem5330249 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term280 _69706 _69704 _69707 _69705) = (term281 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330248 _69705) (@lem5330246 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330250 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term282 _69706 _69704 _69707 _69705) = (term280 _69706 _69704 _69707 _69705).
Proof. exact (@lem17362 (term274 _69705) (term283 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330251 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term282 _69706 _69704 _69707 _69705) = (term281 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330250 _69706 _69704 _69707 _69705) (@lem5330249 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330253 (_69704 : int) : (term270 _69704) = (term270 _69704).
Proof. exact (eq_refl (term270 _69704)). Qed.
Lemma lem5330254 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term284 _69706 _69704 _69707 _69705) = (term285 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330253 _69704) (@lem5330251 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330255 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term286 _69706 _69704 _69707 _69705) = (term284 _69706 _69704 _69707 _69705).
Proof. exact (@lem17362 (term274 _69704) (term287 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330339 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term286 _69706 _69704 _69707 _69705) = (term285 _69706 _69704 _69707 _69705).
Proof. exact (TRANS (@lem5330255 _69706 _69704 _69707 _69705) (@lem5330254 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330342 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330343 (_69704 : int) : (term274 _69704) = (term289 _69704).
Proof. exact (@lem5330342 term290 _69704). Qed.
Lemma lem5330345 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330346 : term292 = term293.
Proof. exact (@lem5330345 (NUMERAL 0)). Qed.
Lemma lem5330347 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330348 : term294 = term295.
Proof. exact (MK_COMB (@lem5330347) (@lem5330346)). Qed.
Lemma lem5330349 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5330350 (_69704 : int) : (term289 _69704) = (term296 _69704).
Proof. exact (MK_COMB (@lem5330348) (@lem5330349 _69704)). Qed.
Lemma lem5330352 (_69704 : int) : (term274 _69704) = (term296 _69704).
Proof. exact (TRANS (@lem5330343 _69704) (@lem5330350 _69704)). Qed.
Lemma lem5330355 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330356 (_69705 : int) : (term274 _69705) = (term289 _69705).
Proof. exact (@lem5330355 term290 _69705). Qed.
Lemma lem5330358 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330359 : term292 = term293.
Proof. exact (@lem5330358 (NUMERAL 0)). Qed.
Lemma lem5330360 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330361 : term294 = term295.
Proof. exact (MK_COMB (@lem5330360) (@lem5330359)). Qed.
Lemma lem5330362 (_69705 : int) : (real_of_int _69705) = (real_of_int _69705).
Proof. exact (eq_refl (real_of_int _69705)). Qed.
Lemma lem5330363 (_69705 : int) : (term289 _69705) = (term296 _69705).
Proof. exact (MK_COMB (@lem5330361) (@lem5330362 _69705)). Qed.
Lemma lem5330365 (_69705 : int) : (term274 _69705) = (term296 _69705).
Proof. exact (TRANS (@lem5330356 _69705) (@lem5330363 _69705)). Qed.
Lemma lem5330368 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330369 (_69706 : int) : (term274 _69706) = (term289 _69706).
Proof. exact (@lem5330368 term290 _69706). Qed.
Lemma lem5330371 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330372 : term292 = term293.
Proof. exact (@lem5330371 (NUMERAL 0)). Qed.
Lemma lem5330373 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330374 : term294 = term295.
Proof. exact (MK_COMB (@lem5330373) (@lem5330372)). Qed.
Lemma lem5330375 (_69706 : int) : (real_of_int _69706) = (real_of_int _69706).
Proof. exact (eq_refl (real_of_int _69706)). Qed.
Lemma lem5330376 (_69706 : int) : (term289 _69706) = (term296 _69706).
Proof. exact (MK_COMB (@lem5330374) (@lem5330375 _69706)). Qed.
Lemma lem5330378 (_69706 : int) : (term274 _69706) = (term296 _69706).
Proof. exact (TRANS (@lem5330369 _69706) (@lem5330376 _69706)). Qed.
Lemma lem5330381 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330382 (_69707 : int) : (term274 _69707) = (term289 _69707).
Proof. exact (@lem5330381 term290 _69707). Qed.
Lemma lem5330384 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330385 : term292 = term293.
Proof. exact (@lem5330384 (NUMERAL 0)). Qed.
Lemma lem5330386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330387 : term294 = term295.
Proof. exact (MK_COMB (@lem5330386) (@lem5330385)). Qed.
Lemma lem5330388 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5330389 (_69707 : int) : (term289 _69707) = (term296 _69707).
Proof. exact (MK_COMB (@lem5330387) (@lem5330388 _69707)). Qed.
Lemma lem5330391 (_69707 : int) : (term274 _69707) = (term296 _69707).
Proof. exact (TRANS (@lem5330382 _69707) (@lem5330389 _69707)). Qed.
Lemma lem5330394 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330395 (_69704 : int) (_69706 : int) : (term210 _69704 _69706) = (term297 _69704 _69706).
Proof. exact (@lem5330394 _69704 (term298 _69706)). Qed.
Lemma lem5330397 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330398 (_69706 : int) : (term301 _69706) = (term302 _69706).
Proof. exact (@lem5330397 _69706 term303). Qed.
Lemma lem5330400 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330401 : term304 = term305.
Proof. exact (@lem5330400 term157). Qed.
Lemma lem5330402 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5330403 (_69706 : int) : (term302 _69706) = (term307 _69706).
Proof. exact (MK_COMB (@lem5330402 _69706) (@lem5330401)). Qed.
Lemma lem5330404 (_69706 : int) : (term301 _69706) = (term307 _69706).
Proof. exact (TRANS (@lem5330398 _69706) (@lem5330403 _69706)). Qed.
Lemma lem5330405 (_69704 : int) : (term308 _69704) = (term308 _69704).
Proof. exact (eq_refl (term308 _69704)). Qed.
Lemma lem5330406 (_69704 : int) (_69706 : int) : (term297 _69704 _69706) = (term309 _69704 _69706).
Proof. exact (MK_COMB (@lem5330405 _69704) (@lem5330404 _69706)). Qed.
Lemma lem5330408 (_69704 : int) (_69706 : int) : (term210 _69704 _69706) = (term309 _69704 _69706).
Proof. exact (TRANS (@lem5330395 _69704 _69706) (@lem5330406 _69704 _69706)). Qed.
Lemma lem5330411 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330413 (_69706 : int) (_69705 : int) : (int_le _69706 _69705) = (term288 _69706 _69705).
Proof. exact (@lem5330411 _69706 _69705). Qed.
Lemma lem5330414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330415 (_69704 : int) (_69706 : int) : (term213 _69704 _69706) = (term310 _69704 _69706).
Proof. exact (MK_COMB (@lem5330414) (@lem5330408 _69704 _69706)). Qed.
Lemma lem5330416 (_69704 : int) (_69706 : int) (_69705 : int) : (term215 _69704 _69706 _69705) = (term311 _69704 _69706 _69705).
Proof. exact (MK_COMB (@lem5330415 _69704 _69706) (@lem5330413 _69706 _69705)). Qed.
Lemma lem5330418 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330419 (_69707 : int) (_69704 : int) : (term218 _69704 _69707) = (term223 _69707 _69704).
Proof. exact (@lem5330418 _69707 _69704). Qed.
Lemma lem5330421 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330422 (_69707 : int) (_69704 : int) : (term223 _69707 _69704) = (term312 _69707 _69704).
Proof. exact (@lem5330421 (term298 _69707) _69704). Qed.
Lemma lem5330424 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330425 (_69707 : int) : (term301 _69707) = (term302 _69707).
Proof. exact (@lem5330424 _69707 term303). Qed.
Lemma lem5330427 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330428 : term304 = term305.
Proof. exact (@lem5330427 term157). Qed.
Lemma lem5330429 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5330430 (_69707 : int) : (term302 _69707) = (term307 _69707).
Proof. exact (MK_COMB (@lem5330429 _69707) (@lem5330428)). Qed.
Lemma lem5330431 (_69707 : int) : (term301 _69707) = (term307 _69707).
Proof. exact (TRANS (@lem5330425 _69707) (@lem5330430 _69707)). Qed.
Lemma lem5330432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330433 (_69707 : int) : (term313 _69707) = (term314 _69707).
Proof. exact (MK_COMB (@lem5330432) (@lem5330431 _69707)). Qed.
Lemma lem5330434 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5330435 (_69707 : int) (_69704 : int) : (term312 _69707 _69704) = (term315 _69707 _69704).
Proof. exact (MK_COMB (@lem5330433 _69707) (@lem5330434 _69704)). Qed.
Lemma lem5330436 (_69707 : int) (_69704 : int) : (term223 _69707 _69704) = (term315 _69707 _69704).
Proof. exact (TRANS (@lem5330422 _69707 _69704) (@lem5330435 _69707 _69704)). Qed.
Lemma lem5330437 (_69707 : int) (_69704 : int) : (term218 _69704 _69707) = (term315 _69707 _69704).
Proof. exact (TRANS (@lem5330419 _69707 _69704) (@lem5330436 _69707 _69704)). Qed.
Lemma lem5330439 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330440 (_69706 : int) (_69707 : int) : (term218 _69707 _69706) = (term223 _69706 _69707).
Proof. exact (@lem5330439 _69706 _69707). Qed.
Lemma lem5330442 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330443 (_69706 : int) (_69707 : int) : (term223 _69706 _69707) = (term312 _69706 _69707).
Proof. exact (@lem5330442 (term298 _69706) _69707). Qed.
Lemma lem5330445 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330446 (_69706 : int) : (term301 _69706) = (term302 _69706).
Proof. exact (@lem5330445 _69706 term303). Qed.
Lemma lem5330448 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330449 : term304 = term305.
Proof. exact (@lem5330448 term157). Qed.
Lemma lem5330450 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5330451 (_69706 : int) : (term302 _69706) = (term307 _69706).
Proof. exact (MK_COMB (@lem5330450 _69706) (@lem5330449)). Qed.
Lemma lem5330452 (_69706 : int) : (term301 _69706) = (term307 _69706).
Proof. exact (TRANS (@lem5330446 _69706) (@lem5330451 _69706)). Qed.
Lemma lem5330453 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330454 (_69706 : int) : (term313 _69706) = (term314 _69706).
Proof. exact (MK_COMB (@lem5330453) (@lem5330452 _69706)). Qed.
Lemma lem5330455 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5330456 (_69706 : int) (_69707 : int) : (term312 _69706 _69707) = (term315 _69706 _69707).
Proof. exact (MK_COMB (@lem5330454 _69706) (@lem5330455 _69707)). Qed.
Lemma lem5330457 (_69706 : int) (_69707 : int) : (term223 _69706 _69707) = (term315 _69706 _69707).
Proof. exact (TRANS (@lem5330443 _69706 _69707) (@lem5330456 _69706 _69707)). Qed.
Lemma lem5330458 (_69706 : int) (_69707 : int) : (term218 _69707 _69706) = (term315 _69706 _69707).
Proof. exact (TRANS (@lem5330440 _69706 _69707) (@lem5330457 _69706 _69707)). Qed.
Lemma lem5330459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330460 (_69707 : int) (_69704 : int) : (term316 _69704 _69707) = (term317 _69707 _69704).
Proof. exact (MK_COMB (@lem5330459) (@lem5330437 _69707 _69704)). Qed.
Lemma lem5330461 (_69704 : int) (_69706 : int) (_69707 : int) : (term220 _69704 _69707 _69706) = (term318 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5330460 _69707 _69704) (@lem5330458 _69706 _69707)). Qed.
Lemma lem5330463 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330464 (_69707 : int) (_69706 : int) : (term246 _69706 _69707) = (term319 _69707 _69706).
Proof. exact (@lem5330463 _69707 (term298 _69706)). Qed.
Lemma lem5330466 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330467 (_69707 : int) (_69706 : int) : (term319 _69707 _69706) = (term320 _69707 _69706).
Proof. exact (@lem5330466 (term298 _69707) (term298 _69706)). Qed.
Lemma lem5330469 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330470 (_69707 : int) : (term301 _69707) = (term302 _69707).
Proof. exact (@lem5330469 _69707 term303). Qed.
Lemma lem5330472 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330473 : term304 = term305.
Proof. exact (@lem5330472 term157). Qed.
Lemma lem5330474 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5330475 (_69707 : int) : (term302 _69707) = (term307 _69707).
Proof. exact (MK_COMB (@lem5330474 _69707) (@lem5330473)). Qed.
Lemma lem5330476 (_69707 : int) : (term301 _69707) = (term307 _69707).
Proof. exact (TRANS (@lem5330470 _69707) (@lem5330475 _69707)). Qed.
Lemma lem5330477 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330478 (_69707 : int) : (term313 _69707) = (term314 _69707).
Proof. exact (MK_COMB (@lem5330477) (@lem5330476 _69707)). Qed.
Lemma lem5330480 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330481 (_69706 : int) : (term301 _69706) = (term302 _69706).
Proof. exact (@lem5330480 _69706 term303). Qed.
Lemma lem5330483 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330484 : term304 = term305.
Proof. exact (@lem5330483 term157). Qed.
Lemma lem5330485 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5330486 (_69706 : int) : (term302 _69706) = (term307 _69706).
Proof. exact (MK_COMB (@lem5330485 _69706) (@lem5330484)). Qed.
Lemma lem5330487 (_69706 : int) : (term301 _69706) = (term307 _69706).
Proof. exact (TRANS (@lem5330481 _69706) (@lem5330486 _69706)). Qed.
Lemma lem5330488 (_69707 : int) (_69706 : int) : (term320 _69707 _69706) = (term321 _69707 _69706).
Proof. exact (MK_COMB (@lem5330478 _69707) (@lem5330487 _69706)). Qed.
Lemma lem5330489 (_69707 : int) (_69706 : int) : (term319 _69707 _69706) = (term321 _69707 _69706).
Proof. exact (TRANS (@lem5330467 _69707 _69706) (@lem5330488 _69707 _69706)). Qed.
Lemma lem5330490 (_69707 : int) (_69706 : int) : (term246 _69706 _69707) = (term321 _69707 _69706).
Proof. exact (TRANS (@lem5330464 _69707 _69706) (@lem5330489 _69707 _69706)). Qed.
Lemma lem5330492 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330493 (_69705 : int) (_69707 : int) : (term218 _69707 _69705) = (term223 _69705 _69707).
Proof. exact (@lem5330492 _69705 _69707). Qed.
Lemma lem5330495 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330496 (_69705 : int) (_69707 : int) : (term223 _69705 _69707) = (term312 _69705 _69707).
Proof. exact (@lem5330495 (term298 _69705) _69707). Qed.
Lemma lem5330498 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330499 (_69705 : int) : (term301 _69705) = (term302 _69705).
Proof. exact (@lem5330498 _69705 term303). Qed.
Lemma lem5330501 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330502 : term304 = term305.
Proof. exact (@lem5330501 term157). Qed.
Lemma lem5330503 (_69705 : int) : (term306 _69705) = (term306 _69705).
Proof. exact (eq_refl (term306 _69705)). Qed.
Lemma lem5330504 (_69705 : int) : (term302 _69705) = (term307 _69705).
Proof. exact (MK_COMB (@lem5330503 _69705) (@lem5330502)). Qed.
Lemma lem5330505 (_69705 : int) : (term301 _69705) = (term307 _69705).
Proof. exact (TRANS (@lem5330499 _69705) (@lem5330504 _69705)). Qed.
Lemma lem5330506 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330507 (_69705 : int) : (term313 _69705) = (term314 _69705).
Proof. exact (MK_COMB (@lem5330506) (@lem5330505 _69705)). Qed.
Lemma lem5330508 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5330509 (_69705 : int) (_69707 : int) : (term312 _69705 _69707) = (term315 _69705 _69707).
Proof. exact (MK_COMB (@lem5330507 _69705) (@lem5330508 _69707)). Qed.
Lemma lem5330510 (_69705 : int) (_69707 : int) : (term223 _69705 _69707) = (term315 _69705 _69707).
Proof. exact (TRANS (@lem5330496 _69705 _69707) (@lem5330509 _69705 _69707)). Qed.
Lemma lem5330511 (_69705 : int) (_69707 : int) : (term218 _69707 _69705) = (term315 _69705 _69707).
Proof. exact (TRANS (@lem5330493 _69705 _69707) (@lem5330510 _69705 _69707)). Qed.
Lemma lem5330512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330513 (_69707 : int) (_69706 : int) : (term322 _69706 _69707) = (term323 _69707 _69706).
Proof. exact (MK_COMB (@lem5330512) (@lem5330490 _69707 _69706)). Qed.
Lemma lem5330514 (_69706 : int) (_69705 : int) (_69707 : int) : (term222 _69706 _69707 _69705) = (term324 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5330513 _69707 _69706) (@lem5330511 _69705 _69707)). Qed.
Lemma lem5330515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330516 (_69704 : int) (_69706 : int) (_69707 : int) : (term225 _69704 _69707 _69706) = (term325 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5330515) (@lem5330461 _69704 _69706 _69707)). Qed.
Lemma lem5330517 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term227 _69704 _69706 _69707 _69705) = (term326 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5330516 _69704 _69706 _69707) (@lem5330514 _69706 _69705 _69707)). Qed.
Lemma lem5330520 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330522 (_69704 : int) (_69707 : int) : (int_le _69704 _69707) = (term288 _69704 _69707).
Proof. exact (@lem5330520 _69704 _69707). Qed.
Lemma lem5330525 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330527 (_69707 : int) (_69705 : int) : (int_le _69707 _69705) = (term288 _69707 _69705).
Proof. exact (@lem5330525 _69707 _69705). Qed.
Lemma lem5330528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330529 (_69704 : int) (_69707 : int) : (term232 _69704 _69707) = (term327 _69704 _69707).
Proof. exact (MK_COMB (@lem5330528) (@lem5330522 _69704 _69707)). Qed.
Lemma lem5330530 (_69704 : int) (_69707 : int) (_69705 : int) : (term229 _69704 _69707 _69705) = (term328 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330529 _69704 _69707) (@lem5330527 _69707 _69705)). Qed.
Lemma lem5330531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330532 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term236 _69704 _69706 _69707 _69705) = (term329 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5330531) (@lem5330517 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5330533 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term238 _69706 _69704 _69707 _69705) = (term330 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330532 _69704 _69706 _69705 _69707) (@lem5330530 _69704 _69707 _69705)). Qed.
Lemma lem5330536 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330538 (_69704 : int) (_69707 : int) : (int_le _69704 _69707) = (term288 _69704 _69707).
Proof. exact (@lem5330536 _69704 _69707). Qed.
Lemma lem5330541 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330543 (_69707 : int) (_69706 : int) : (int_le _69707 _69706) = (term288 _69707 _69706).
Proof. exact (@lem5330541 _69707 _69706). Qed.
Lemma lem5330544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330545 (_69704 : int) (_69707 : int) : (term232 _69704 _69707) = (term327 _69704 _69707).
Proof. exact (MK_COMB (@lem5330544) (@lem5330538 _69704 _69707)). Qed.
Lemma lem5330546 (_69704 : int) (_69707 : int) (_69706 : int) : (term229 _69704 _69707 _69706) = (term328 _69704 _69707 _69706).
Proof. exact (MK_COMB (@lem5330545 _69704 _69707) (@lem5330543 _69707 _69706)). Qed.
Lemma lem5330549 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330550 (_69706 : int) (_69707 : int) : (term223 _69706 _69707) = (term312 _69706 _69707).
Proof. exact (@lem5330549 (term298 _69706) _69707). Qed.
Lemma lem5330552 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330553 (_69706 : int) : (term301 _69706) = (term302 _69706).
Proof. exact (@lem5330552 _69706 term303). Qed.
Lemma lem5330555 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330556 : term304 = term305.
Proof. exact (@lem5330555 term157). Qed.
Lemma lem5330557 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5330558 (_69706 : int) : (term302 _69706) = (term307 _69706).
Proof. exact (MK_COMB (@lem5330557 _69706) (@lem5330556)). Qed.
Lemma lem5330559 (_69706 : int) : (term301 _69706) = (term307 _69706).
Proof. exact (TRANS (@lem5330553 _69706) (@lem5330558 _69706)). Qed.
Lemma lem5330560 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330561 (_69706 : int) : (term313 _69706) = (term314 _69706).
Proof. exact (MK_COMB (@lem5330560) (@lem5330559 _69706)). Qed.
Lemma lem5330562 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5330563 (_69706 : int) (_69707 : int) : (term312 _69706 _69707) = (term315 _69706 _69707).
Proof. exact (MK_COMB (@lem5330561 _69706) (@lem5330562 _69707)). Qed.
Lemma lem5330565 (_69706 : int) (_69707 : int) : (term223 _69706 _69707) = (term315 _69706 _69707).
Proof. exact (TRANS (@lem5330550 _69706 _69707) (@lem5330563 _69706 _69707)). Qed.
Lemma lem5330568 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330570 (_69707 : int) (_69705 : int) : (int_le _69707 _69705) = (term288 _69707 _69705).
Proof. exact (@lem5330568 _69707 _69705). Qed.
Lemma lem5330571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330572 (_69706 : int) (_69707 : int) : (term243 _69706 _69707) = (term331 _69706 _69707).
Proof. exact (MK_COMB (@lem5330571) (@lem5330565 _69706 _69707)). Qed.
Lemma lem5330573 (_69706 : int) (_69707 : int) (_69705 : int) : (term230 _69706 _69707 _69705) = (term332 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330572 _69706 _69707) (@lem5330570 _69707 _69705)). Qed.
Lemma lem5330574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330575 (_69704 : int) (_69707 : int) (_69706 : int) : (term248 _69704 _69707 _69706) = (term333 _69704 _69707 _69706).
Proof. exact (MK_COMB (@lem5330574) (@lem5330546 _69704 _69707 _69706)). Qed.
Lemma lem5330576 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term240 _69704 _69706 _69707 _69705) = (term334 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330575 _69704 _69707 _69706) (@lem5330573 _69706 _69707 _69705)). Qed.
Lemma lem5330578 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330579 (_69707 : int) (_69704 : int) : (term218 _69704 _69707) = (term223 _69707 _69704).
Proof. exact (@lem5330578 _69707 _69704). Qed.
Lemma lem5330581 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330582 (_69707 : int) (_69704 : int) : (term223 _69707 _69704) = (term312 _69707 _69704).
Proof. exact (@lem5330581 (term298 _69707) _69704). Qed.
Lemma lem5330584 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330585 (_69707 : int) : (term301 _69707) = (term302 _69707).
Proof. exact (@lem5330584 _69707 term303). Qed.
Lemma lem5330587 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330588 : term304 = term305.
Proof. exact (@lem5330587 term157). Qed.
Lemma lem5330589 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5330590 (_69707 : int) : (term302 _69707) = (term307 _69707).
Proof. exact (MK_COMB (@lem5330589 _69707) (@lem5330588)). Qed.
Lemma lem5330591 (_69707 : int) : (term301 _69707) = (term307 _69707).
Proof. exact (TRANS (@lem5330585 _69707) (@lem5330590 _69707)). Qed.
Lemma lem5330592 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330593 (_69707 : int) : (term313 _69707) = (term314 _69707).
Proof. exact (MK_COMB (@lem5330592) (@lem5330591 _69707)). Qed.
Lemma lem5330594 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5330595 (_69707 : int) (_69704 : int) : (term312 _69707 _69704) = (term315 _69707 _69704).
Proof. exact (MK_COMB (@lem5330593 _69707) (@lem5330594 _69704)). Qed.
Lemma lem5330596 (_69707 : int) (_69704 : int) : (term223 _69707 _69704) = (term315 _69707 _69704).
Proof. exact (TRANS (@lem5330582 _69707 _69704) (@lem5330595 _69707 _69704)). Qed.
Lemma lem5330597 (_69707 : int) (_69704 : int) : (term218 _69704 _69707) = (term315 _69707 _69704).
Proof. exact (TRANS (@lem5330579 _69707 _69704) (@lem5330596 _69707 _69704)). Qed.
Lemma lem5330599 (y : int) (x : int) : (term218 x y) = (term223 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5330600 (_69705 : int) (_69707 : int) : (term218 _69707 _69705) = (term223 _69705 _69707).
Proof. exact (@lem5330599 _69705 _69707). Qed.
Lemma lem5330602 (x : int) (y : int) : (int_le x y) = (term288 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5330603 (_69705 : int) (_69707 : int) : (term223 _69705 _69707) = (term312 _69705 _69707).
Proof. exact (@lem5330602 (term298 _69705) _69707). Qed.
Lemma lem5330605 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5330606 (_69705 : int) : (term301 _69705) = (term302 _69705).
Proof. exact (@lem5330605 _69705 term303). Qed.
Lemma lem5330608 (n : nat) : (term291 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5330609 : term304 = term305.
Proof. exact (@lem5330608 term157). Qed.
Lemma lem5330610 (_69705 : int) : (term306 _69705) = (term306 _69705).
Proof. exact (eq_refl (term306 _69705)). Qed.
Lemma lem5330611 (_69705 : int) : (term302 _69705) = (term307 _69705).
Proof. exact (MK_COMB (@lem5330610 _69705) (@lem5330609)). Qed.
Lemma lem5330612 (_69705 : int) : (term301 _69705) = (term307 _69705).
Proof. exact (TRANS (@lem5330606 _69705) (@lem5330611 _69705)). Qed.
Lemma lem5330613 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5330614 (_69705 : int) : (term313 _69705) = (term314 _69705).
Proof. exact (MK_COMB (@lem5330613) (@lem5330612 _69705)). Qed.
Lemma lem5330615 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5330616 (_69705 : int) (_69707 : int) : (term312 _69705 _69707) = (term315 _69705 _69707).
Proof. exact (MK_COMB (@lem5330614 _69705) (@lem5330615 _69707)). Qed.
Lemma lem5330617 (_69705 : int) (_69707 : int) : (term223 _69705 _69707) = (term315 _69705 _69707).
Proof. exact (TRANS (@lem5330603 _69705 _69707) (@lem5330616 _69705 _69707)). Qed.
Lemma lem5330618 (_69705 : int) (_69707 : int) : (term218 _69707 _69705) = (term315 _69705 _69707).
Proof. exact (TRANS (@lem5330600 _69705 _69707) (@lem5330617 _69705 _69707)). Qed.
Lemma lem5330619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330620 (_69707 : int) (_69704 : int) : (term316 _69704 _69707) = (term317 _69707 _69704).
Proof. exact (MK_COMB (@lem5330619) (@lem5330597 _69707 _69704)). Qed.
Lemma lem5330621 (_69704 : int) (_69705 : int) (_69707 : int) : (term220 _69704 _69707 _69705) = (term318 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330620 _69707 _69704) (@lem5330618 _69705 _69707)). Qed.
Lemma lem5330622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330623 (_69704 : int) (_69706 : int) (_69707 : int) (_69705 : int) : (term252 _69704 _69706 _69707 _69705) = (term335 _69704 _69706 _69707 _69705).
Proof. exact (MK_COMB (@lem5330622) (@lem5330576 _69704 _69706 _69707 _69705)). Qed.
Lemma lem5330624 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term254 _69706 _69704 _69707 _69705) = (term336 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330623 _69704 _69706 _69707 _69705) (@lem5330621 _69704 _69705 _69707)). Qed.
Lemma lem5330625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5330626 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term257 _69706 _69704 _69707 _69705) = (term337 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5330625) (@lem5330533 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5330627 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term259 _69706 _69704 _69707 _69705) = (term338 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330626 _69706 _69704 _69707 _69705) (@lem5330624 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330629 (_69704 : int) (_69706 : int) (_69705 : int) : (term264 _69704 _69706 _69705) = (term339 _69704 _69706 _69705).
Proof. exact (MK_COMB (@lem5330628) (@lem5330416 _69704 _69706 _69705)). Qed.
Lemma lem5330630 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term266 _69706 _69704 _69707 _69705) = (term340 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330629 _69704 _69706 _69705) (@lem5330627 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330632 (_69707 : int) : (term270 _69707) = (term341 _69707).
Proof. exact (MK_COMB (@lem5330631) (@lem5330391 _69707)). Qed.
Lemma lem5330633 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term272 _69706 _69704 _69707 _69705) = (term342 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330632 _69707) (@lem5330630 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330635 (_69706 : int) : (term270 _69706) = (term341 _69706).
Proof. exact (MK_COMB (@lem5330634) (@lem5330378 _69706)). Qed.
Lemma lem5330636 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term277 _69706 _69704 _69707 _69705) = (term343 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330635 _69706) (@lem5330633 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330638 (_69705 : int) : (term270 _69705) = (term341 _69705).
Proof. exact (MK_COMB (@lem5330637) (@lem5330365 _69705)). Qed.
Lemma lem5330639 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term281 _69706 _69704 _69707 _69705) = (term344 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330638 _69705) (@lem5330636 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5330641 (_69704 : int) : (term270 _69704) = (term341 _69704).
Proof. exact (MK_COMB (@lem5330640) (@lem5330352 _69704)). Qed.
Lemma lem5330642 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term285 _69706 _69704 _69707 _69705) = (term345 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5330641 _69704) (@lem5330639 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330643 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term286 _69706 _69704 _69707 _69705) = (term345 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5330339 _69706 _69704 _69707 _69705) (@lem5330642 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330647 (t : Prop) : (term346 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5330823 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term347 _69706 _69704 _69705 _69707) = (term345 _69706 _69704 _69705 _69707).
Proof. exact (@lem5330647 (term345 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5330824 (_69704 : int) : (term296 _69704) = (term348 _69704).
Proof. exact (@lem1988287 (real_of_int _69704) term293). Qed.
Lemma lem5330830 (_69704 : int) : (term349 _69704) = (term350 _69704).
Proof. exact (@lem1982792 (real_of_int _69704) term293). Qed.
Lemma lem5330832 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5330833 : term293 = term352.
Proof. exact (@lem5330832 (NUMERAL 0)). Qed.
Lemma lem5330835 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5330836 : term355 = term356.
Proof. exact (@lem5330835 term157). Qed.
Lemma lem5330837 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5330838 : term357 = term358.
Proof. exact (MK_COMB (@lem5330837) (@lem5330836)). Qed.
Lemma lem5330839 : term359 = term360.
Proof. exact (MK_COMB (@lem5330838) (@lem5330833)). Qed.
Lemma lem5330840 : term360 = term361.
Proof. exact (@lem1981613 term355 term293 term305 term305). Qed.
Lemma lem5330842 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5330843 : term364 = term365.
Proof. exact (@lem5330842 term157 term157). Qed.
Lemma lem5330844 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5330845 : term367 = term157.
Proof. exact (EQ_MP (@lem5330844) (@lem940073)). Qed.
Lemma lem5330846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5330847 : term365 = term305.
Proof. exact (MK_COMB (@lem5330846) (@lem5330845)). Qed.
Lemma lem5330848 : term364 = term305.
Proof. exact (TRANS (@lem5330843) (@lem5330847)). Qed.
Lemma lem5330850 (x : nat) : (term368 x) = term293.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5330851 : term359 = term293.
Proof. exact (@lem5330850 term157). Qed.
Lemma lem5330852 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5330853 : term369 = term370.
Proof. exact (MK_COMB (@lem5330852) (@lem5330851)). Qed.
Lemma lem5330854 : term361 = term352.
Proof. exact (MK_COMB (@lem5330853) (@lem5330848)). Qed.
Lemma lem5330855 : term360 = term352.
Proof. exact (TRANS (@lem5330840) (@lem5330854)). Qed.
Lemma lem5330856 : term359 = term352.
Proof. exact (TRANS (@lem5330839) (@lem5330855)). Qed.
Lemma lem5330858 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5330859 : term352 = term293.
Proof. exact (@lem5330858 term293). Qed.
Lemma lem5330860 : term359 = term293.
Proof. exact (TRANS (@lem5330856) (@lem5330859)). Qed.
Lemma lem5330861 (_69704 : int) : (term306 _69704) = (term306 _69704).
Proof. exact (eq_refl (term306 _69704)). Qed.
Lemma lem5330862 (_69704 : int) : (term350 _69704) = (term372 _69704).
Proof. exact (MK_COMB (@lem5330861 _69704) (@lem5330860)). Qed.
Lemma lem5330863 (_69704 : int) : (term372 _69704) = (real_of_int _69704).
Proof. exact (@lem1982723 (real_of_int _69704)). Qed.
Lemma lem5330864 (_69704 : int) : (term350 _69704) = (real_of_int _69704).
Proof. exact (TRANS (@lem5330862 _69704) (@lem5330863 _69704)). Qed.
Lemma lem5330866 (_69704 : int) : (term349 _69704) = (real_of_int _69704).
Proof. exact (TRANS (@lem5330830 _69704) (@lem5330864 _69704)). Qed.
Lemma lem5330867 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5330868 (_69704 : int) : (term373 _69704) = (term374 _69704).
Proof. exact (MK_COMB (@lem5330867) (@lem5330866 _69704)). Qed.
Lemma lem5330869 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5330870 (_69704 : int) : (term348 _69704) = (term375 _69704).
Proof. exact (MK_COMB (@lem5330868 _69704) (@lem5330869)). Qed.
Lemma lem5330871 (_69704 : int) : (term296 _69704) = (term375 _69704).
Proof. exact (TRANS (@lem5330824 _69704) (@lem5330870 _69704)). Qed.
Lemma lem5330872 (_69705 : int) : (term296 _69705) = (term348 _69705).
Proof. exact (@lem1988287 (real_of_int _69705) term293). Qed.
Lemma lem5330878 (_69705 : int) : (term349 _69705) = (term350 _69705).
Proof. exact (@lem1982792 (real_of_int _69705) term293). Qed.
Lemma lem5330880 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5330881 : term293 = term352.
Proof. exact (@lem5330880 (NUMERAL 0)). Qed.
Lemma lem5330883 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5330884 : term355 = term356.
Proof. exact (@lem5330883 term157). Qed.
Lemma lem5330885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5330886 : term357 = term358.
Proof. exact (MK_COMB (@lem5330885) (@lem5330884)). Qed.
Lemma lem5330887 : term359 = term360.
Proof. exact (MK_COMB (@lem5330886) (@lem5330881)). Qed.
Lemma lem5330888 : term360 = term361.
Proof. exact (@lem1981613 term355 term293 term305 term305). Qed.
Lemma lem5330890 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5330891 : term364 = term365.
Proof. exact (@lem5330890 term157 term157). Qed.
Lemma lem5330892 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5330893 : term367 = term157.
Proof. exact (EQ_MP (@lem5330892) (@lem940073)). Qed.
Lemma lem5330894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5330895 : term365 = term305.
Proof. exact (MK_COMB (@lem5330894) (@lem5330893)). Qed.
Lemma lem5330896 : term364 = term305.
Proof. exact (TRANS (@lem5330891) (@lem5330895)). Qed.
Lemma lem5330898 (x : nat) : (term368 x) = term293.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5330899 : term359 = term293.
Proof. exact (@lem5330898 term157). Qed.
Lemma lem5330900 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5330901 : term369 = term370.
Proof. exact (MK_COMB (@lem5330900) (@lem5330899)). Qed.
Lemma lem5330902 : term361 = term352.
Proof. exact (MK_COMB (@lem5330901) (@lem5330896)). Qed.
Lemma lem5330903 : term360 = term352.
Proof. exact (TRANS (@lem5330888) (@lem5330902)). Qed.
Lemma lem5330904 : term359 = term352.
Proof. exact (TRANS (@lem5330887) (@lem5330903)). Qed.
Lemma lem5330906 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5330907 : term352 = term293.
Proof. exact (@lem5330906 term293). Qed.
Lemma lem5330908 : term359 = term293.
Proof. exact (TRANS (@lem5330904) (@lem5330907)). Qed.
Lemma lem5330909 (_69705 : int) : (term306 _69705) = (term306 _69705).
Proof. exact (eq_refl (term306 _69705)). Qed.
Lemma lem5330910 (_69705 : int) : (term350 _69705) = (term372 _69705).
Proof. exact (MK_COMB (@lem5330909 _69705) (@lem5330908)). Qed.
Lemma lem5330911 (_69705 : int) : (term372 _69705) = (real_of_int _69705).
Proof. exact (@lem1982723 (real_of_int _69705)). Qed.
Lemma lem5330912 (_69705 : int) : (term350 _69705) = (real_of_int _69705).
Proof. exact (TRANS (@lem5330910 _69705) (@lem5330911 _69705)). Qed.
Lemma lem5330914 (_69705 : int) : (term349 _69705) = (real_of_int _69705).
Proof. exact (TRANS (@lem5330878 _69705) (@lem5330912 _69705)). Qed.
Lemma lem5330915 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5330916 (_69705 : int) : (term373 _69705) = (term374 _69705).
Proof. exact (MK_COMB (@lem5330915) (@lem5330914 _69705)). Qed.
Lemma lem5330917 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5330918 (_69705 : int) : (term348 _69705) = (term375 _69705).
Proof. exact (MK_COMB (@lem5330916 _69705) (@lem5330917)). Qed.
Lemma lem5330919 (_69705 : int) : (term296 _69705) = (term375 _69705).
Proof. exact (TRANS (@lem5330872 _69705) (@lem5330918 _69705)). Qed.
Lemma lem5330920 (_69706 : int) : (term296 _69706) = (term348 _69706).
Proof. exact (@lem1988287 (real_of_int _69706) term293). Qed.
Lemma lem5330926 (_69706 : int) : (term349 _69706) = (term350 _69706).
Proof. exact (@lem1982792 (real_of_int _69706) term293). Qed.
Lemma lem5330928 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5330929 : term293 = term352.
Proof. exact (@lem5330928 (NUMERAL 0)). Qed.
Lemma lem5330931 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5330932 : term355 = term356.
Proof. exact (@lem5330931 term157). Qed.
Lemma lem5330933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5330934 : term357 = term358.
Proof. exact (MK_COMB (@lem5330933) (@lem5330932)). Qed.
Lemma lem5330935 : term359 = term360.
Proof. exact (MK_COMB (@lem5330934) (@lem5330929)). Qed.
Lemma lem5330936 : term360 = term361.
Proof. exact (@lem1981613 term355 term293 term305 term305). Qed.
Lemma lem5330938 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5330939 : term364 = term365.
Proof. exact (@lem5330938 term157 term157). Qed.
Lemma lem5330940 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5330941 : term367 = term157.
Proof. exact (EQ_MP (@lem5330940) (@lem940073)). Qed.
Lemma lem5330942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5330943 : term365 = term305.
Proof. exact (MK_COMB (@lem5330942) (@lem5330941)). Qed.
Lemma lem5330944 : term364 = term305.
Proof. exact (TRANS (@lem5330939) (@lem5330943)). Qed.
Lemma lem5330946 (x : nat) : (term368 x) = term293.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5330947 : term359 = term293.
Proof. exact (@lem5330946 term157). Qed.
Lemma lem5330948 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5330949 : term369 = term370.
Proof. exact (MK_COMB (@lem5330948) (@lem5330947)). Qed.
Lemma lem5330950 : term361 = term352.
Proof. exact (MK_COMB (@lem5330949) (@lem5330944)). Qed.
Lemma lem5330951 : term360 = term352.
Proof. exact (TRANS (@lem5330936) (@lem5330950)). Qed.
Lemma lem5330952 : term359 = term352.
Proof. exact (TRANS (@lem5330935) (@lem5330951)). Qed.
Lemma lem5330954 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5330955 : term352 = term293.
Proof. exact (@lem5330954 term293). Qed.
Lemma lem5330956 : term359 = term293.
Proof. exact (TRANS (@lem5330952) (@lem5330955)). Qed.
Lemma lem5330957 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5330958 (_69706 : int) : (term350 _69706) = (term372 _69706).
Proof. exact (MK_COMB (@lem5330957 _69706) (@lem5330956)). Qed.
Lemma lem5330959 (_69706 : int) : (term372 _69706) = (real_of_int _69706).
Proof. exact (@lem1982723 (real_of_int _69706)). Qed.
Lemma lem5330960 (_69706 : int) : (term350 _69706) = (real_of_int _69706).
Proof. exact (TRANS (@lem5330958 _69706) (@lem5330959 _69706)). Qed.
Lemma lem5330962 (_69706 : int) : (term349 _69706) = (real_of_int _69706).
Proof. exact (TRANS (@lem5330926 _69706) (@lem5330960 _69706)). Qed.
Lemma lem5330963 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5330964 (_69706 : int) : (term373 _69706) = (term374 _69706).
Proof. exact (MK_COMB (@lem5330963) (@lem5330962 _69706)). Qed.
Lemma lem5330965 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5330966 (_69706 : int) : (term348 _69706) = (term375 _69706).
Proof. exact (MK_COMB (@lem5330964 _69706) (@lem5330965)). Qed.
Lemma lem5330967 (_69706 : int) : (term296 _69706) = (term375 _69706).
Proof. exact (TRANS (@lem5330920 _69706) (@lem5330966 _69706)). Qed.
Lemma lem5330968 (_69707 : int) : (term296 _69707) = (term348 _69707).
Proof. exact (@lem1988287 (real_of_int _69707) term293). Qed.
Lemma lem5330974 (_69707 : int) : (term349 _69707) = (term350 _69707).
Proof. exact (@lem1982792 (real_of_int _69707) term293). Qed.
Lemma lem5330976 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5330977 : term293 = term352.
Proof. exact (@lem5330976 (NUMERAL 0)). Qed.
Lemma lem5330979 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5330980 : term355 = term356.
Proof. exact (@lem5330979 term157). Qed.
Lemma lem5330981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5330982 : term357 = term358.
Proof. exact (MK_COMB (@lem5330981) (@lem5330980)). Qed.
Lemma lem5330983 : term359 = term360.
Proof. exact (MK_COMB (@lem5330982) (@lem5330977)). Qed.
Lemma lem5330984 : term360 = term361.
Proof. exact (@lem1981613 term355 term293 term305 term305). Qed.
Lemma lem5330986 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5330987 : term364 = term365.
Proof. exact (@lem5330986 term157 term157). Qed.
Lemma lem5330988 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5330989 : term367 = term157.
Proof. exact (EQ_MP (@lem5330988) (@lem940073)). Qed.
Lemma lem5330990 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5330991 : term365 = term305.
Proof. exact (MK_COMB (@lem5330990) (@lem5330989)). Qed.
Lemma lem5330992 : term364 = term305.
Proof. exact (TRANS (@lem5330987) (@lem5330991)). Qed.
Lemma lem5330994 (x : nat) : (term368 x) = term293.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5330995 : term359 = term293.
Proof. exact (@lem5330994 term157). Qed.
Lemma lem5330996 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5330997 : term369 = term370.
Proof. exact (MK_COMB (@lem5330996) (@lem5330995)). Qed.
Lemma lem5330998 : term361 = term352.
Proof. exact (MK_COMB (@lem5330997) (@lem5330992)). Qed.
Lemma lem5330999 : term360 = term352.
Proof. exact (TRANS (@lem5330984) (@lem5330998)). Qed.
Lemma lem5331000 : term359 = term352.
Proof. exact (TRANS (@lem5330983) (@lem5330999)). Qed.
Lemma lem5331002 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331003 : term352 = term293.
Proof. exact (@lem5331002 term293). Qed.
Lemma lem5331004 : term359 = term293.
Proof. exact (TRANS (@lem5331000) (@lem5331003)). Qed.
Lemma lem5331005 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5331006 (_69707 : int) : (term350 _69707) = (term372 _69707).
Proof. exact (MK_COMB (@lem5331005 _69707) (@lem5331004)). Qed.
Lemma lem5331007 (_69707 : int) : (term372 _69707) = (real_of_int _69707).
Proof. exact (@lem1982723 (real_of_int _69707)). Qed.
Lemma lem5331008 (_69707 : int) : (term350 _69707) = (real_of_int _69707).
Proof. exact (TRANS (@lem5331006 _69707) (@lem5331007 _69707)). Qed.
Lemma lem5331010 (_69707 : int) : (term349 _69707) = (real_of_int _69707).
Proof. exact (TRANS (@lem5330974 _69707) (@lem5331008 _69707)). Qed.
Lemma lem5331011 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331012 (_69707 : int) : (term373 _69707) = (term374 _69707).
Proof. exact (MK_COMB (@lem5331011) (@lem5331010 _69707)). Qed.
Lemma lem5331013 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331014 (_69707 : int) : (term348 _69707) = (term375 _69707).
Proof. exact (MK_COMB (@lem5331012 _69707) (@lem5331013)). Qed.
Lemma lem5331015 (_69707 : int) : (term296 _69707) = (term375 _69707).
Proof. exact (TRANS (@lem5330968 _69707) (@lem5331014 _69707)). Qed.
Lemma lem5331016 (_69706 : int) (_69704 : int) : (term309 _69704 _69706) = (term376 _69706 _69704).
Proof. exact (@lem1988287 (term307 _69706) (real_of_int _69704)). Qed.
Lemma lem5331028 (_69706 : int) (_69704 : int) : (term377 _69706 _69704) = (term378 _69706 _69704).
Proof. exact (@lem1982792 (term307 _69706) (real_of_int _69704)). Qed.
Lemma lem5331033 (_69704 : int) (_69706 : int) : (term378 _69706 _69704) = (term379 _69704 _69706).
Proof. exact (@lem1982761 (term380 _69704) (term307 _69706)). Qed.
Lemma lem5331035 (_69704 : int) (_69706 : int) : (term377 _69706 _69704) = (term379 _69704 _69706).
Proof. exact (TRANS (@lem5331028 _69706 _69704) (@lem5331033 _69704 _69706)). Qed.
Lemma lem5331036 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331037 (_69704 : int) (_69706 : int) : (term381 _69706 _69704) = (term382 _69704 _69706).
Proof. exact (MK_COMB (@lem5331036) (@lem5331035 _69704 _69706)). Qed.
Lemma lem5331038 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331039 (_69704 : int) (_69706 : int) : (term376 _69706 _69704) = (term383 _69704 _69706).
Proof. exact (MK_COMB (@lem5331037 _69704 _69706) (@lem5331038)). Qed.
Lemma lem5331040 (_69704 : int) (_69706 : int) : (term309 _69704 _69706) = (term383 _69704 _69706).
Proof. exact (TRANS (@lem5331016 _69706 _69704) (@lem5331039 _69704 _69706)). Qed.
Lemma lem5331041 (_69705 : int) (_69706 : int) : (term288 _69706 _69705) = (term384 _69705 _69706).
Proof. exact (@lem1988287 (real_of_int _69705) (real_of_int _69706)). Qed.
Lemma lem5331054 (_69705 : int) (_69706 : int) : (term385 _69705 _69706) = (term386 _69705 _69706).
Proof. exact (@lem1982792 (real_of_int _69705) (real_of_int _69706)). Qed.
Lemma lem5331055 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331056 (_69705 : int) (_69706 : int) : (term387 _69705 _69706) = (term388 _69705 _69706).
Proof. exact (MK_COMB (@lem5331055) (@lem5331054 _69705 _69706)). Qed.
Lemma lem5331057 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331058 (_69705 : int) (_69706 : int) : (term384 _69705 _69706) = (term389 _69705 _69706).
Proof. exact (MK_COMB (@lem5331056 _69705 _69706) (@lem5331057)). Qed.
Lemma lem5331059 (_69705 : int) (_69706 : int) : (term288 _69706 _69705) = (term389 _69705 _69706).
Proof. exact (TRANS (@lem5331041 _69705 _69706) (@lem5331058 _69705 _69706)). Qed.
Lemma lem5331060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331061 (_69704 : int) (_69706 : int) : (term310 _69704 _69706) = (term390 _69704 _69706).
Proof. exact (MK_COMB (@lem5331060) (@lem5331040 _69704 _69706)). Qed.
Lemma lem5331062 (_69704 : int) (_69705 : int) (_69706 : int) : (term311 _69704 _69706 _69705) = (term391 _69704 _69705 _69706).
Proof. exact (MK_COMB (@lem5331061 _69704 _69706) (@lem5331059 _69705 _69706)). Qed.
Lemma lem5331063 (_69704 : int) (_69707 : int) : (term315 _69707 _69704) = (term392 _69704 _69707).
Proof. exact (@lem1988287 (real_of_int _69704) (term307 _69707)). Qed.
Lemma lem5331075 (_69704 : int) (_69707 : int) : (term393 _69704 _69707) = (term394 _69704 _69707).
Proof. exact (@lem1982792 (real_of_int _69704) (term307 _69707)). Qed.
Lemma lem5331076 (_69707 : int) : (term395 _69707) = (term396 _69707).
Proof. exact (@lem1982781 (real_of_int _69707) term355 term305). Qed.
Lemma lem5331078 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331079 : term305 = term397.
Proof. exact (@lem5331078 term157). Qed.
Lemma lem5331081 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331082 : term355 = term356.
Proof. exact (@lem5331081 term157). Qed.
Lemma lem5331083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331084 : term357 = term358.
Proof. exact (MK_COMB (@lem5331083) (@lem5331082)). Qed.
Lemma lem5331085 : term398 = term399.
Proof. exact (MK_COMB (@lem5331084) (@lem5331079)). Qed.
Lemma lem5331086 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331088 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331089 : term364 = term365.
Proof. exact (@lem5331088 term157 term157). Qed.
Lemma lem5331090 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331091 : term367 = term157.
Proof. exact (EQ_MP (@lem5331090) (@lem940073)). Qed.
Lemma lem5331092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331093 : term365 = term305.
Proof. exact (MK_COMB (@lem5331092) (@lem5331091)). Qed.
Lemma lem5331094 : term364 = term305.
Proof. exact (TRANS (@lem5331089) (@lem5331093)). Qed.
Lemma lem5331096 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331097 : term398 = term403.
Proof. exact (@lem5331096 term157 term157). Qed.
Lemma lem5331098 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331099 : term367 = term157.
Proof. exact (EQ_MP (@lem5331098) (@lem940073)). Qed.
Lemma lem5331100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331101 : term365 = term305.
Proof. exact (MK_COMB (@lem5331100) (@lem5331099)). Qed.
Lemma lem5331102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331103 : term403 = term355.
Proof. exact (MK_COMB (@lem5331102) (@lem5331101)). Qed.
Lemma lem5331104 : term398 = term355.
Proof. exact (TRANS (@lem5331097) (@lem5331103)). Qed.
Lemma lem5331105 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331106 : term404 = term405.
Proof. exact (MK_COMB (@lem5331105) (@lem5331104)). Qed.
Lemma lem5331107 : term400 = term356.
Proof. exact (MK_COMB (@lem5331106) (@lem5331094)). Qed.
Lemma lem5331108 : term399 = term356.
Proof. exact (TRANS (@lem5331086) (@lem5331107)). Qed.
Lemma lem5331109 : term398 = term356.
Proof. exact (TRANS (@lem5331085) (@lem5331108)). Qed.
Lemma lem5331111 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331112 : term356 = term355.
Proof. exact (@lem5331111 term355). Qed.
Lemma lem5331113 : term398 = term355.
Proof. exact (TRANS (@lem5331109) (@lem5331112)). Qed.
Lemma lem5331116 (_69707 : int) : (term406 _69707) = (term406 _69707).
Proof. exact (eq_refl (term406 _69707)). Qed.
Lemma lem5331117 (_69707 : int) : (term396 _69707) = (term407 _69707).
Proof. exact (MK_COMB (@lem5331116 _69707) (@lem5331113)). Qed.
Lemma lem5331118 (_69707 : int) : (term395 _69707) = (term407 _69707).
Proof. exact (TRANS (@lem5331076 _69707) (@lem5331117 _69707)). Qed.
Lemma lem5331119 (_69704 : int) : (term306 _69704) = (term306 _69704).
Proof. exact (eq_refl (term306 _69704)). Qed.
Lemma lem5331122 (_69704 : int) (_69707 : int) : (term394 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (MK_COMB (@lem5331119 _69704) (@lem5331118 _69707)). Qed.
Lemma lem5331124 (_69704 : int) (_69707 : int) : (term393 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (TRANS (@lem5331075 _69704 _69707) (@lem5331122 _69704 _69707)). Qed.
Lemma lem5331125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331126 (_69704 : int) (_69707 : int) : (term409 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5331125) (@lem5331124 _69704 _69707)). Qed.
Lemma lem5331127 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331128 (_69704 : int) (_69707 : int) : (term392 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5331126 _69704 _69707) (@lem5331127)). Qed.
Lemma lem5331129 (_69704 : int) (_69707 : int) : (term315 _69707 _69704) = (term411 _69704 _69707).
Proof. exact (TRANS (@lem5331063 _69704 _69707) (@lem5331128 _69704 _69707)). Qed.
Lemma lem5331130 (_69707 : int) (_69706 : int) : (term315 _69706 _69707) = (term392 _69707 _69706).
Proof. exact (@lem1988287 (real_of_int _69707) (term307 _69706)). Qed.
Lemma lem5331142 (_69707 : int) (_69706 : int) : (term393 _69707 _69706) = (term394 _69707 _69706).
Proof. exact (@lem1982792 (real_of_int _69707) (term307 _69706)). Qed.
Lemma lem5331143 (_69706 : int) : (term395 _69706) = (term396 _69706).
Proof. exact (@lem1982781 (real_of_int _69706) term355 term305). Qed.
Lemma lem5331145 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331146 : term305 = term397.
Proof. exact (@lem5331145 term157). Qed.
Lemma lem5331148 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331149 : term355 = term356.
Proof. exact (@lem5331148 term157). Qed.
Lemma lem5331150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331151 : term357 = term358.
Proof. exact (MK_COMB (@lem5331150) (@lem5331149)). Qed.
Lemma lem5331152 : term398 = term399.
Proof. exact (MK_COMB (@lem5331151) (@lem5331146)). Qed.
Lemma lem5331153 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331155 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331156 : term364 = term365.
Proof. exact (@lem5331155 term157 term157). Qed.
Lemma lem5331157 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331158 : term367 = term157.
Proof. exact (EQ_MP (@lem5331157) (@lem940073)). Qed.
Lemma lem5331159 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331160 : term365 = term305.
Proof. exact (MK_COMB (@lem5331159) (@lem5331158)). Qed.
Lemma lem5331161 : term364 = term305.
Proof. exact (TRANS (@lem5331156) (@lem5331160)). Qed.
Lemma lem5331163 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331164 : term398 = term403.
Proof. exact (@lem5331163 term157 term157). Qed.
Lemma lem5331165 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331166 : term367 = term157.
Proof. exact (EQ_MP (@lem5331165) (@lem940073)). Qed.
Lemma lem5331167 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331168 : term365 = term305.
Proof. exact (MK_COMB (@lem5331167) (@lem5331166)). Qed.
Lemma lem5331169 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331170 : term403 = term355.
Proof. exact (MK_COMB (@lem5331169) (@lem5331168)). Qed.
Lemma lem5331171 : term398 = term355.
Proof. exact (TRANS (@lem5331164) (@lem5331170)). Qed.
Lemma lem5331172 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331173 : term404 = term405.
Proof. exact (MK_COMB (@lem5331172) (@lem5331171)). Qed.
Lemma lem5331174 : term400 = term356.
Proof. exact (MK_COMB (@lem5331173) (@lem5331161)). Qed.
Lemma lem5331175 : term399 = term356.
Proof. exact (TRANS (@lem5331153) (@lem5331174)). Qed.
Lemma lem5331176 : term398 = term356.
Proof. exact (TRANS (@lem5331152) (@lem5331175)). Qed.
Lemma lem5331178 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331179 : term356 = term355.
Proof. exact (@lem5331178 term355). Qed.
Lemma lem5331180 : term398 = term355.
Proof. exact (TRANS (@lem5331176) (@lem5331179)). Qed.
Lemma lem5331183 (_69706 : int) : (term406 _69706) = (term406 _69706).
Proof. exact (eq_refl (term406 _69706)). Qed.
Lemma lem5331184 (_69706 : int) : (term396 _69706) = (term407 _69706).
Proof. exact (MK_COMB (@lem5331183 _69706) (@lem5331180)). Qed.
Lemma lem5331185 (_69706 : int) : (term395 _69706) = (term407 _69706).
Proof. exact (TRANS (@lem5331143 _69706) (@lem5331184 _69706)). Qed.
Lemma lem5331186 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5331187 (_69707 : int) (_69706 : int) : (term394 _69707 _69706) = (term408 _69707 _69706).
Proof. exact (MK_COMB (@lem5331186 _69707) (@lem5331185 _69706)). Qed.
Lemma lem5331192 (_69706 : int) (_69707 : int) : (term408 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (@lem1982757 (term380 _69706) (real_of_int _69707) term355). Qed.
Lemma lem5331193 (_69706 : int) (_69707 : int) : (term394 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (TRANS (@lem5331187 _69707 _69706) (@lem5331192 _69706 _69707)). Qed.
Lemma lem5331195 (_69706 : int) (_69707 : int) : (term393 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (TRANS (@lem5331142 _69707 _69706) (@lem5331193 _69706 _69707)). Qed.
Lemma lem5331196 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331197 (_69706 : int) (_69707 : int) : (term409 _69707 _69706) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5331196) (@lem5331195 _69706 _69707)). Qed.
Lemma lem5331198 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331199 (_69706 : int) (_69707 : int) : (term392 _69707 _69706) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5331197 _69706 _69707) (@lem5331198)). Qed.
Lemma lem5331200 (_69706 : int) (_69707 : int) : (term315 _69706 _69707) = (term414 _69706 _69707).
Proof. exact (TRANS (@lem5331130 _69707 _69706) (@lem5331199 _69706 _69707)). Qed.
Lemma lem5331201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331202 (_69704 : int) (_69707 : int) : (term317 _69707 _69704) = (term415 _69704 _69707).
Proof. exact (MK_COMB (@lem5331201) (@lem5331129 _69704 _69707)). Qed.
Lemma lem5331203 (_69704 : int) (_69706 : int) (_69707 : int) : (term318 _69704 _69706 _69707) = (term416 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5331202 _69704 _69707) (@lem5331200 _69706 _69707)). Qed.
Lemma lem5331204 (_69706 : int) (_69707 : int) : (term321 _69707 _69706) = (term417 _69706 _69707).
Proof. exact (@lem1988287 (term307 _69706) (term307 _69707)). Qed.
Lemma lem5331222 (_69706 : int) (_69707 : int) : (term418 _69706 _69707) = (term419 _69706 _69707).
Proof. exact (@lem1982792 (term307 _69706) (term307 _69707)). Qed.
Lemma lem5331223 (_69707 : int) : (term395 _69707) = (term396 _69707).
Proof. exact (@lem1982781 (real_of_int _69707) term355 term305). Qed.
Lemma lem5331225 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331226 : term305 = term397.
Proof. exact (@lem5331225 term157). Qed.
Lemma lem5331228 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331229 : term355 = term356.
Proof. exact (@lem5331228 term157). Qed.
Lemma lem5331230 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331231 : term357 = term358.
Proof. exact (MK_COMB (@lem5331230) (@lem5331229)). Qed.
Lemma lem5331232 : term398 = term399.
Proof. exact (MK_COMB (@lem5331231) (@lem5331226)). Qed.
Lemma lem5331233 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331235 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331236 : term364 = term365.
Proof. exact (@lem5331235 term157 term157). Qed.
Lemma lem5331237 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331238 : term367 = term157.
Proof. exact (EQ_MP (@lem5331237) (@lem940073)). Qed.
Lemma lem5331239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331240 : term365 = term305.
Proof. exact (MK_COMB (@lem5331239) (@lem5331238)). Qed.
Lemma lem5331241 : term364 = term305.
Proof. exact (TRANS (@lem5331236) (@lem5331240)). Qed.
Lemma lem5331243 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331244 : term398 = term403.
Proof. exact (@lem5331243 term157 term157). Qed.
Lemma lem5331245 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331246 : term367 = term157.
Proof. exact (EQ_MP (@lem5331245) (@lem940073)). Qed.
Lemma lem5331247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331248 : term365 = term305.
Proof. exact (MK_COMB (@lem5331247) (@lem5331246)). Qed.
Lemma lem5331249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331250 : term403 = term355.
Proof. exact (MK_COMB (@lem5331249) (@lem5331248)). Qed.
Lemma lem5331251 : term398 = term355.
Proof. exact (TRANS (@lem5331244) (@lem5331250)). Qed.
Lemma lem5331252 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331253 : term404 = term405.
Proof. exact (MK_COMB (@lem5331252) (@lem5331251)). Qed.
Lemma lem5331254 : term400 = term356.
Proof. exact (MK_COMB (@lem5331253) (@lem5331241)). Qed.
Lemma lem5331255 : term399 = term356.
Proof. exact (TRANS (@lem5331233) (@lem5331254)). Qed.
Lemma lem5331256 : term398 = term356.
Proof. exact (TRANS (@lem5331232) (@lem5331255)). Qed.
Lemma lem5331258 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331259 : term356 = term355.
Proof. exact (@lem5331258 term355). Qed.
Lemma lem5331260 : term398 = term355.
Proof. exact (TRANS (@lem5331256) (@lem5331259)). Qed.
Lemma lem5331263 (_69707 : int) : (term406 _69707) = (term406 _69707).
Proof. exact (eq_refl (term406 _69707)). Qed.
Lemma lem5331264 (_69707 : int) : (term396 _69707) = (term407 _69707).
Proof. exact (MK_COMB (@lem5331263 _69707) (@lem5331260)). Qed.
Lemma lem5331265 (_69707 : int) : (term395 _69707) = (term407 _69707).
Proof. exact (TRANS (@lem5331223 _69707) (@lem5331264 _69707)). Qed.
Lemma lem5331266 (_69706 : int) : (term420 _69706) = (term420 _69706).
Proof. exact (eq_refl (term420 _69706)). Qed.
Lemma lem5331267 (_69706 : int) (_69707 : int) : (term419 _69706 _69707) = (term421 _69706 _69707).
Proof. exact (MK_COMB (@lem5331266 _69706) (@lem5331265 _69707)). Qed.
Lemma lem5331268 (_69706 : int) (_69707 : int) : (term421 _69706 _69707) = (term422 _69706 _69707).
Proof. exact (@lem1982755 (real_of_int _69706) term305 (term407 _69707)). Qed.
Lemma lem5331269 (_69707 : int) : (term423 _69707) = (term424 _69707).
Proof. exact (@lem1982757 (term380 _69707) term305 term355). Qed.
Lemma lem5331271 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331272 : term355 = term356.
Proof. exact (@lem5331271 term157). Qed.
Lemma lem5331274 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331275 : term305 = term397.
Proof. exact (@lem5331274 term157). Qed.
Lemma lem5331276 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5331277 : term425 = term426.
Proof. exact (MK_COMB (@lem5331276) (@lem5331275)). Qed.
Lemma lem5331278 : term427 = term428.
Proof. exact (MK_COMB (@lem5331277) (@lem5331272)). Qed.
Lemma lem5331279 : term429.
Proof. exact (@lem1981473 term305 term305 term355 term305 term293 term305). Qed.
Lemma lem5331281 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5331282 : term431 = term432.
Proof. exact (@lem5331281 (NUMERAL 0) term157). Qed.
Lemma lem5331283 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5331284 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5331285 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5331284 h1) (fun h1 : term432 = True => @lem5331283)). Qed.
Lemma lem5331286 : term432 = True.
Proof. exact (EQ_MP (@lem5331285) (@lem5331283)). Qed.
Lemma lem5331287 : term431 = True.
Proof. exact (TRANS (@lem5331282) (@lem5331286)). Qed.
Lemma lem5331288 : True = term431.
Proof. exact (SYM (@lem5331287)). Qed.
Lemma lem5331289 : term431.
Proof. exact (EQ_MP (@lem5331288) (@lem0)). Qed.
Lemma lem5331290 : term434.
Proof. exact (@lem5331279 (@lem5331289)). Qed.
Lemma lem5331292 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5331293 : term431 = term432.
Proof. exact (@lem5331292 (NUMERAL 0) term157). Qed.
Lemma lem5331294 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5331295 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5331296 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5331295 h1) (fun h1 : term432 = True => @lem5331294)). Qed.
Lemma lem5331297 : term432 = True.
Proof. exact (EQ_MP (@lem5331296) (@lem5331294)). Qed.
Lemma lem5331298 : term431 = True.
Proof. exact (TRANS (@lem5331293) (@lem5331297)). Qed.
Lemma lem5331299 : True = term431.
Proof. exact (SYM (@lem5331298)). Qed.
Lemma lem5331300 : term431.
Proof. exact (EQ_MP (@lem5331299) (@lem0)). Qed.
Lemma lem5331301 : term435.
Proof. exact (@lem5331290 (@lem5331300)). Qed.
Lemma lem5331303 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5331304 : term431 = term432.
Proof. exact (@lem5331303 (NUMERAL 0) term157). Qed.
Lemma lem5331305 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5331306 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5331307 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5331306 h1) (fun h1 : term432 = True => @lem5331305)). Qed.
Lemma lem5331308 : term432 = True.
Proof. exact (EQ_MP (@lem5331307) (@lem5331305)). Qed.
Lemma lem5331309 : term431 = True.
Proof. exact (TRANS (@lem5331304) (@lem5331308)). Qed.
Lemma lem5331310 : True = term431.
Proof. exact (SYM (@lem5331309)). Qed.
Lemma lem5331311 : term431.
Proof. exact (EQ_MP (@lem5331310) (@lem0)). Qed.
Lemma lem5331312 : term436.
Proof. exact (@lem5331301 (@lem5331311)). Qed.
Lemma lem5331314 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331315 : term398 = term403.
Proof. exact (@lem5331314 term157 term157). Qed.
Lemma lem5331316 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331317 : term367 = term157.
Proof. exact (EQ_MP (@lem5331316) (@lem940073)). Qed.
Lemma lem5331318 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331319 : term365 = term305.
Proof. exact (MK_COMB (@lem5331318) (@lem5331317)). Qed.
Lemma lem5331320 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331321 : term403 = term355.
Proof. exact (MK_COMB (@lem5331320) (@lem5331319)). Qed.
Lemma lem5331322 : term398 = term355.
Proof. exact (TRANS (@lem5331315) (@lem5331321)). Qed.
Lemma lem5331324 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331325 : term364 = term365.
Proof. exact (@lem5331324 term157 term157). Qed.
Lemma lem5331326 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331327 : term367 = term157.
Proof. exact (EQ_MP (@lem5331326) (@lem940073)). Qed.
Lemma lem5331328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331329 : term365 = term305.
Proof. exact (MK_COMB (@lem5331328) (@lem5331327)). Qed.
Lemma lem5331330 : term364 = term305.
Proof. exact (TRANS (@lem5331325) (@lem5331329)). Qed.
Lemma lem5331331 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5331332 : term437 = term425.
Proof. exact (MK_COMB (@lem5331331) (@lem5331330)). Qed.
Lemma lem5331333 : term438 = term427.
Proof. exact (MK_COMB (@lem5331332) (@lem5331322)). Qed.
Lemma lem5331335 (m : nat) : (term439 m) = term293.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5331336 : term427 = term293.
Proof. exact (@lem5331335 term157). Qed.
Lemma lem5331337 : term438 = term293.
Proof. exact (TRANS (@lem5331333) (@lem5331336)). Qed.
Lemma lem5331338 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331339 : term440 = term441.
Proof. exact (MK_COMB (@lem5331338) (@lem5331337)). Qed.
Lemma lem5331340 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5331341 : term442 = term443.
Proof. exact (MK_COMB (@lem5331339) (@lem5331340)). Qed.
Lemma lem5331343 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5331344 : term443 = term293.
Proof. exact (@lem5331343 term157). Qed.
Lemma lem5331345 : term442 = term293.
Proof. exact (TRANS (@lem5331341) (@lem5331344)). Qed.
Lemma lem5331347 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331348 : term364 = term365.
Proof. exact (@lem5331347 term157 term157). Qed.
Lemma lem5331349 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331350 : term367 = term157.
Proof. exact (EQ_MP (@lem5331349) (@lem940073)). Qed.
Lemma lem5331351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331352 : term365 = term305.
Proof. exact (MK_COMB (@lem5331351) (@lem5331350)). Qed.
Lemma lem5331353 : term364 = term305.
Proof. exact (TRANS (@lem5331348) (@lem5331352)). Qed.
Lemma lem5331354 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5331355 : term445 = term443.
Proof. exact (MK_COMB (@lem5331354) (@lem5331353)). Qed.
Lemma lem5331357 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5331358 : term443 = term293.
Proof. exact (@lem5331357 term157). Qed.
Lemma lem5331359 : term445 = term293.
Proof. exact (TRANS (@lem5331355) (@lem5331358)). Qed.
Lemma lem5331360 : term293 = term445.
Proof. exact (SYM (@lem5331359)). Qed.
Lemma lem5331361 : term442 = term445.
Proof. exact (TRANS (@lem5331345) (@lem5331360)). Qed.
Lemma lem5331362 : term428 = term352.
Proof. exact (@lem5331312 (@lem5331361)). Qed.
Lemma lem5331363 : term427 = term352.
Proof. exact (TRANS (@lem5331278) (@lem5331362)). Qed.
Lemma lem5331365 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5331366 : term352 = term293.
Proof. exact (@lem5331365 term293). Qed.
Lemma lem5331367 : term427 = term293.
Proof. exact (TRANS (@lem5331363) (@lem5331366)). Qed.
Lemma lem5331368 (_69707 : int) : (term406 _69707) = (term406 _69707).
Proof. exact (eq_refl (term406 _69707)). Qed.
Lemma lem5331369 (_69707 : int) : (term424 _69707) = (term446 _69707).
Proof. exact (MK_COMB (@lem5331368 _69707) (@lem5331367)). Qed.
Lemma lem5331370 (_69707 : int) : (term423 _69707) = (term446 _69707).
Proof. exact (TRANS (@lem5331269 _69707) (@lem5331369 _69707)). Qed.
Lemma lem5331371 (_69707 : int) : (term446 _69707) = (term380 _69707).
Proof. exact (@lem1982723 (term380 _69707)). Qed.
Lemma lem5331372 (_69707 : int) : (term423 _69707) = (term380 _69707).
Proof. exact (TRANS (@lem5331370 _69707) (@lem5331371 _69707)). Qed.
Lemma lem5331373 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5331374 (_69706 : int) (_69707 : int) : (term422 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (MK_COMB (@lem5331373 _69706) (@lem5331372 _69707)). Qed.
Lemma lem5331375 (_69706 : int) (_69707 : int) : (term421 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (TRANS (@lem5331268 _69706 _69707) (@lem5331374 _69706 _69707)). Qed.
Lemma lem5331376 (_69706 : int) (_69707 : int) : (term419 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (TRANS (@lem5331267 _69706 _69707) (@lem5331375 _69706 _69707)). Qed.
Lemma lem5331378 (_69706 : int) (_69707 : int) : (term418 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (TRANS (@lem5331222 _69706 _69707) (@lem5331376 _69706 _69707)). Qed.
Lemma lem5331379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331380 (_69706 : int) (_69707 : int) : (term447 _69706 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5331379) (@lem5331378 _69706 _69707)). Qed.
Lemma lem5331381 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331382 (_69706 : int) (_69707 : int) : (term417 _69706 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5331380 _69706 _69707) (@lem5331381)). Qed.
Lemma lem5331383 (_69706 : int) (_69707 : int) : (term321 _69707 _69706) = (term389 _69706 _69707).
Proof. exact (TRANS (@lem5331204 _69706 _69707) (@lem5331382 _69706 _69707)). Qed.
Lemma lem5331384 (_69707 : int) (_69705 : int) : (term315 _69705 _69707) = (term392 _69707 _69705).
Proof. exact (@lem1988287 (real_of_int _69707) (term307 _69705)). Qed.
Lemma lem5331396 (_69707 : int) (_69705 : int) : (term393 _69707 _69705) = (term394 _69707 _69705).
Proof. exact (@lem1982792 (real_of_int _69707) (term307 _69705)). Qed.
Lemma lem5331397 (_69705 : int) : (term395 _69705) = (term396 _69705).
Proof. exact (@lem1982781 (real_of_int _69705) term355 term305). Qed.
Lemma lem5331399 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331400 : term305 = term397.
Proof. exact (@lem5331399 term157). Qed.
Lemma lem5331402 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331403 : term355 = term356.
Proof. exact (@lem5331402 term157). Qed.
Lemma lem5331404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331405 : term357 = term358.
Proof. exact (MK_COMB (@lem5331404) (@lem5331403)). Qed.
Lemma lem5331406 : term398 = term399.
Proof. exact (MK_COMB (@lem5331405) (@lem5331400)). Qed.
Lemma lem5331407 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331409 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331410 : term364 = term365.
Proof. exact (@lem5331409 term157 term157). Qed.
Lemma lem5331411 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331412 : term367 = term157.
Proof. exact (EQ_MP (@lem5331411) (@lem940073)). Qed.
Lemma lem5331413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331414 : term365 = term305.
Proof. exact (MK_COMB (@lem5331413) (@lem5331412)). Qed.
Lemma lem5331415 : term364 = term305.
Proof. exact (TRANS (@lem5331410) (@lem5331414)). Qed.
Lemma lem5331417 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331418 : term398 = term403.
Proof. exact (@lem5331417 term157 term157). Qed.
Lemma lem5331419 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331420 : term367 = term157.
Proof. exact (EQ_MP (@lem5331419) (@lem940073)). Qed.
Lemma lem5331421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331422 : term365 = term305.
Proof. exact (MK_COMB (@lem5331421) (@lem5331420)). Qed.
Lemma lem5331423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331424 : term403 = term355.
Proof. exact (MK_COMB (@lem5331423) (@lem5331422)). Qed.
Lemma lem5331425 : term398 = term355.
Proof. exact (TRANS (@lem5331418) (@lem5331424)). Qed.
Lemma lem5331426 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331427 : term404 = term405.
Proof. exact (MK_COMB (@lem5331426) (@lem5331425)). Qed.
Lemma lem5331428 : term400 = term356.
Proof. exact (MK_COMB (@lem5331427) (@lem5331415)). Qed.
Lemma lem5331429 : term399 = term356.
Proof. exact (TRANS (@lem5331407) (@lem5331428)). Qed.
Lemma lem5331430 : term398 = term356.
Proof. exact (TRANS (@lem5331406) (@lem5331429)). Qed.
Lemma lem5331432 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331433 : term356 = term355.
Proof. exact (@lem5331432 term355). Qed.
Lemma lem5331434 : term398 = term355.
Proof. exact (TRANS (@lem5331430) (@lem5331433)). Qed.
Lemma lem5331437 (_69705 : int) : (term406 _69705) = (term406 _69705).
Proof. exact (eq_refl (term406 _69705)). Qed.
Lemma lem5331438 (_69705 : int) : (term396 _69705) = (term407 _69705).
Proof. exact (MK_COMB (@lem5331437 _69705) (@lem5331434)). Qed.
Lemma lem5331439 (_69705 : int) : (term395 _69705) = (term407 _69705).
Proof. exact (TRANS (@lem5331397 _69705) (@lem5331438 _69705)). Qed.
Lemma lem5331440 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5331441 (_69707 : int) (_69705 : int) : (term394 _69707 _69705) = (term408 _69707 _69705).
Proof. exact (MK_COMB (@lem5331440 _69707) (@lem5331439 _69705)). Qed.
Lemma lem5331446 (_69705 : int) (_69707 : int) : (term408 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (@lem1982757 (term380 _69705) (real_of_int _69707) term355). Qed.
Lemma lem5331447 (_69705 : int) (_69707 : int) : (term394 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (TRANS (@lem5331441 _69707 _69705) (@lem5331446 _69705 _69707)). Qed.
Lemma lem5331449 (_69705 : int) (_69707 : int) : (term393 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (TRANS (@lem5331396 _69707 _69705) (@lem5331447 _69705 _69707)). Qed.
Lemma lem5331450 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331451 (_69705 : int) (_69707 : int) : (term409 _69707 _69705) = (term413 _69705 _69707).
Proof. exact (MK_COMB (@lem5331450) (@lem5331449 _69705 _69707)). Qed.
Lemma lem5331452 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331453 (_69705 : int) (_69707 : int) : (term392 _69707 _69705) = (term414 _69705 _69707).
Proof. exact (MK_COMB (@lem5331451 _69705 _69707) (@lem5331452)). Qed.
Lemma lem5331454 (_69705 : int) (_69707 : int) : (term315 _69705 _69707) = (term414 _69705 _69707).
Proof. exact (TRANS (@lem5331384 _69707 _69705) (@lem5331453 _69705 _69707)). Qed.
Lemma lem5331455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331456 (_69706 : int) (_69707 : int) : (term323 _69707 _69706) = (term448 _69706 _69707).
Proof. exact (MK_COMB (@lem5331455) (@lem5331383 _69706 _69707)). Qed.
Lemma lem5331457 (_69706 : int) (_69705 : int) (_69707 : int) : (term324 _69706 _69705 _69707) = (term449 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331456 _69706 _69707) (@lem5331454 _69705 _69707)). Qed.
Lemma lem5331458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331459 (_69704 : int) (_69706 : int) (_69707 : int) : (term325 _69704 _69706 _69707) = (term450 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5331458) (@lem5331203 _69704 _69706 _69707)). Qed.
Lemma lem5331460 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term326 _69704 _69706 _69705 _69707) = (term451 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331459 _69704 _69706 _69707) (@lem5331457 _69706 _69705 _69707)). Qed.
Lemma lem5331461 (_69707 : int) (_69704 : int) : (term288 _69704 _69707) = (term384 _69707 _69704).
Proof. exact (@lem1988287 (real_of_int _69707) (real_of_int _69704)). Qed.
Lemma lem5331467 (_69707 : int) (_69704 : int) : (term385 _69707 _69704) = (term386 _69707 _69704).
Proof. exact (@lem1982792 (real_of_int _69707) (real_of_int _69704)). Qed.
Lemma lem5331472 (_69704 : int) (_69707 : int) : (term386 _69707 _69704) = (term452 _69704 _69707).
Proof. exact (@lem1982761 (term380 _69704) (real_of_int _69707)). Qed.
Lemma lem5331474 (_69704 : int) (_69707 : int) : (term385 _69707 _69704) = (term452 _69704 _69707).
Proof. exact (TRANS (@lem5331467 _69707 _69704) (@lem5331472 _69704 _69707)). Qed.
Lemma lem5331475 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331476 (_69704 : int) (_69707 : int) : (term387 _69707 _69704) = (term453 _69704 _69707).
Proof. exact (MK_COMB (@lem5331475) (@lem5331474 _69704 _69707)). Qed.
Lemma lem5331477 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331478 (_69704 : int) (_69707 : int) : (term384 _69707 _69704) = (term454 _69704 _69707).
Proof. exact (MK_COMB (@lem5331476 _69704 _69707) (@lem5331477)). Qed.
Lemma lem5331479 (_69704 : int) (_69707 : int) : (term288 _69704 _69707) = (term454 _69704 _69707).
Proof. exact (TRANS (@lem5331461 _69707 _69704) (@lem5331478 _69704 _69707)). Qed.
Lemma lem5331480 (_69705 : int) (_69707 : int) : (term288 _69707 _69705) = (term384 _69705 _69707).
Proof. exact (@lem1988287 (real_of_int _69705) (real_of_int _69707)). Qed.
Lemma lem5331493 (_69705 : int) (_69707 : int) : (term385 _69705 _69707) = (term386 _69705 _69707).
Proof. exact (@lem1982792 (real_of_int _69705) (real_of_int _69707)). Qed.
Lemma lem5331494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331495 (_69705 : int) (_69707 : int) : (term387 _69705 _69707) = (term388 _69705 _69707).
Proof. exact (MK_COMB (@lem5331494) (@lem5331493 _69705 _69707)). Qed.
Lemma lem5331496 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331497 (_69705 : int) (_69707 : int) : (term384 _69705 _69707) = (term389 _69705 _69707).
Proof. exact (MK_COMB (@lem5331495 _69705 _69707) (@lem5331496)). Qed.
Lemma lem5331498 (_69705 : int) (_69707 : int) : (term288 _69707 _69705) = (term389 _69705 _69707).
Proof. exact (TRANS (@lem5331480 _69705 _69707) (@lem5331497 _69705 _69707)). Qed.
Lemma lem5331499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331500 (_69704 : int) (_69707 : int) : (term327 _69704 _69707) = (term455 _69704 _69707).
Proof. exact (MK_COMB (@lem5331499) (@lem5331479 _69704 _69707)). Qed.
Lemma lem5331501 (_69704 : int) (_69705 : int) (_69707 : int) : (term328 _69704 _69707 _69705) = (term456 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331500 _69704 _69707) (@lem5331498 _69705 _69707)). Qed.
Lemma lem5331502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331503 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term329 _69704 _69706 _69705 _69707) = (term457 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331502) (@lem5331460 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331504 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term330 _69706 _69704 _69707 _69705) = (term458 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331503 _69704 _69706 _69705 _69707) (@lem5331501 _69704 _69705 _69707)). Qed.
Lemma lem5331505 (_69707 : int) (_69704 : int) : (term288 _69704 _69707) = (term384 _69707 _69704).
Proof. exact (@lem1988287 (real_of_int _69707) (real_of_int _69704)). Qed.
Lemma lem5331511 (_69707 : int) (_69704 : int) : (term385 _69707 _69704) = (term386 _69707 _69704).
Proof. exact (@lem1982792 (real_of_int _69707) (real_of_int _69704)). Qed.
Lemma lem5331516 (_69704 : int) (_69707 : int) : (term386 _69707 _69704) = (term452 _69704 _69707).
Proof. exact (@lem1982761 (term380 _69704) (real_of_int _69707)). Qed.
Lemma lem5331518 (_69704 : int) (_69707 : int) : (term385 _69707 _69704) = (term452 _69704 _69707).
Proof. exact (TRANS (@lem5331511 _69707 _69704) (@lem5331516 _69704 _69707)). Qed.
Lemma lem5331519 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331520 (_69704 : int) (_69707 : int) : (term387 _69707 _69704) = (term453 _69704 _69707).
Proof. exact (MK_COMB (@lem5331519) (@lem5331518 _69704 _69707)). Qed.
Lemma lem5331521 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331522 (_69704 : int) (_69707 : int) : (term384 _69707 _69704) = (term454 _69704 _69707).
Proof. exact (MK_COMB (@lem5331520 _69704 _69707) (@lem5331521)). Qed.
Lemma lem5331523 (_69704 : int) (_69707 : int) : (term288 _69704 _69707) = (term454 _69704 _69707).
Proof. exact (TRANS (@lem5331505 _69707 _69704) (@lem5331522 _69704 _69707)). Qed.
Lemma lem5331524 (_69706 : int) (_69707 : int) : (term288 _69707 _69706) = (term384 _69706 _69707).
Proof. exact (@lem1988287 (real_of_int _69706) (real_of_int _69707)). Qed.
Lemma lem5331537 (_69706 : int) (_69707 : int) : (term385 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (@lem1982792 (real_of_int _69706) (real_of_int _69707)). Qed.
Lemma lem5331538 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331539 (_69706 : int) (_69707 : int) : (term387 _69706 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5331538) (@lem5331537 _69706 _69707)). Qed.
Lemma lem5331540 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331541 (_69706 : int) (_69707 : int) : (term384 _69706 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5331539 _69706 _69707) (@lem5331540)). Qed.
Lemma lem5331542 (_69706 : int) (_69707 : int) : (term288 _69707 _69706) = (term389 _69706 _69707).
Proof. exact (TRANS (@lem5331524 _69706 _69707) (@lem5331541 _69706 _69707)). Qed.
Lemma lem5331543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331544 (_69704 : int) (_69707 : int) : (term327 _69704 _69707) = (term455 _69704 _69707).
Proof. exact (MK_COMB (@lem5331543) (@lem5331523 _69704 _69707)). Qed.
Lemma lem5331545 (_69704 : int) (_69706 : int) (_69707 : int) : (term328 _69704 _69707 _69706) = (term456 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5331544 _69704 _69707) (@lem5331542 _69706 _69707)). Qed.
Lemma lem5331546 (_69707 : int) (_69706 : int) : (term315 _69706 _69707) = (term392 _69707 _69706).
Proof. exact (@lem1988287 (real_of_int _69707) (term307 _69706)). Qed.
Lemma lem5331558 (_69707 : int) (_69706 : int) : (term393 _69707 _69706) = (term394 _69707 _69706).
Proof. exact (@lem1982792 (real_of_int _69707) (term307 _69706)). Qed.
Lemma lem5331559 (_69706 : int) : (term395 _69706) = (term396 _69706).
Proof. exact (@lem1982781 (real_of_int _69706) term355 term305). Qed.
Lemma lem5331561 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331562 : term305 = term397.
Proof. exact (@lem5331561 term157). Qed.
Lemma lem5331564 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331565 : term355 = term356.
Proof. exact (@lem5331564 term157). Qed.
Lemma lem5331566 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331567 : term357 = term358.
Proof. exact (MK_COMB (@lem5331566) (@lem5331565)). Qed.
Lemma lem5331568 : term398 = term399.
Proof. exact (MK_COMB (@lem5331567) (@lem5331562)). Qed.
Lemma lem5331569 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331571 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331572 : term364 = term365.
Proof. exact (@lem5331571 term157 term157). Qed.
Lemma lem5331573 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331574 : term367 = term157.
Proof. exact (EQ_MP (@lem5331573) (@lem940073)). Qed.
Lemma lem5331575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331576 : term365 = term305.
Proof. exact (MK_COMB (@lem5331575) (@lem5331574)). Qed.
Lemma lem5331577 : term364 = term305.
Proof. exact (TRANS (@lem5331572) (@lem5331576)). Qed.
Lemma lem5331579 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331580 : term398 = term403.
Proof. exact (@lem5331579 term157 term157). Qed.
Lemma lem5331581 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331582 : term367 = term157.
Proof. exact (EQ_MP (@lem5331581) (@lem940073)). Qed.
Lemma lem5331583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331584 : term365 = term305.
Proof. exact (MK_COMB (@lem5331583) (@lem5331582)). Qed.
Lemma lem5331585 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331586 : term403 = term355.
Proof. exact (MK_COMB (@lem5331585) (@lem5331584)). Qed.
Lemma lem5331587 : term398 = term355.
Proof. exact (TRANS (@lem5331580) (@lem5331586)). Qed.
Lemma lem5331588 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331589 : term404 = term405.
Proof. exact (MK_COMB (@lem5331588) (@lem5331587)). Qed.
Lemma lem5331590 : term400 = term356.
Proof. exact (MK_COMB (@lem5331589) (@lem5331577)). Qed.
Lemma lem5331591 : term399 = term356.
Proof. exact (TRANS (@lem5331569) (@lem5331590)). Qed.
Lemma lem5331592 : term398 = term356.
Proof. exact (TRANS (@lem5331568) (@lem5331591)). Qed.
Lemma lem5331594 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331595 : term356 = term355.
Proof. exact (@lem5331594 term355). Qed.
Lemma lem5331596 : term398 = term355.
Proof. exact (TRANS (@lem5331592) (@lem5331595)). Qed.
Lemma lem5331599 (_69706 : int) : (term406 _69706) = (term406 _69706).
Proof. exact (eq_refl (term406 _69706)). Qed.
Lemma lem5331600 (_69706 : int) : (term396 _69706) = (term407 _69706).
Proof. exact (MK_COMB (@lem5331599 _69706) (@lem5331596)). Qed.
Lemma lem5331601 (_69706 : int) : (term395 _69706) = (term407 _69706).
Proof. exact (TRANS (@lem5331559 _69706) (@lem5331600 _69706)). Qed.
Lemma lem5331602 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5331603 (_69707 : int) (_69706 : int) : (term394 _69707 _69706) = (term408 _69707 _69706).
Proof. exact (MK_COMB (@lem5331602 _69707) (@lem5331601 _69706)). Qed.
Lemma lem5331608 (_69706 : int) (_69707 : int) : (term408 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (@lem1982757 (term380 _69706) (real_of_int _69707) term355). Qed.
Lemma lem5331609 (_69706 : int) (_69707 : int) : (term394 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (TRANS (@lem5331603 _69707 _69706) (@lem5331608 _69706 _69707)). Qed.
Lemma lem5331611 (_69706 : int) (_69707 : int) : (term393 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (TRANS (@lem5331558 _69707 _69706) (@lem5331609 _69706 _69707)). Qed.
Lemma lem5331612 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331613 (_69706 : int) (_69707 : int) : (term409 _69707 _69706) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5331612) (@lem5331611 _69706 _69707)). Qed.
Lemma lem5331614 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331615 (_69706 : int) (_69707 : int) : (term392 _69707 _69706) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5331613 _69706 _69707) (@lem5331614)). Qed.
Lemma lem5331616 (_69706 : int) (_69707 : int) : (term315 _69706 _69707) = (term414 _69706 _69707).
Proof. exact (TRANS (@lem5331546 _69707 _69706) (@lem5331615 _69706 _69707)). Qed.
Lemma lem5331617 (_69705 : int) (_69707 : int) : (term288 _69707 _69705) = (term384 _69705 _69707).
Proof. exact (@lem1988287 (real_of_int _69705) (real_of_int _69707)). Qed.
Lemma lem5331630 (_69705 : int) (_69707 : int) : (term385 _69705 _69707) = (term386 _69705 _69707).
Proof. exact (@lem1982792 (real_of_int _69705) (real_of_int _69707)). Qed.
Lemma lem5331631 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331632 (_69705 : int) (_69707 : int) : (term387 _69705 _69707) = (term388 _69705 _69707).
Proof. exact (MK_COMB (@lem5331631) (@lem5331630 _69705 _69707)). Qed.
Lemma lem5331633 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331634 (_69705 : int) (_69707 : int) : (term384 _69705 _69707) = (term389 _69705 _69707).
Proof. exact (MK_COMB (@lem5331632 _69705 _69707) (@lem5331633)). Qed.
Lemma lem5331635 (_69705 : int) (_69707 : int) : (term288 _69707 _69705) = (term389 _69705 _69707).
Proof. exact (TRANS (@lem5331617 _69705 _69707) (@lem5331634 _69705 _69707)). Qed.
Lemma lem5331636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331637 (_69706 : int) (_69707 : int) : (term331 _69706 _69707) = (term459 _69706 _69707).
Proof. exact (MK_COMB (@lem5331636) (@lem5331616 _69706 _69707)). Qed.
Lemma lem5331638 (_69706 : int) (_69705 : int) (_69707 : int) : (term332 _69706 _69707 _69705) = (term460 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331637 _69706 _69707) (@lem5331635 _69705 _69707)). Qed.
Lemma lem5331639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331640 (_69704 : int) (_69706 : int) (_69707 : int) : (term333 _69704 _69707 _69706) = (term461 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5331639) (@lem5331545 _69704 _69706 _69707)). Qed.
Lemma lem5331641 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term334 _69704 _69706 _69707 _69705) = (term462 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331640 _69704 _69706 _69707) (@lem5331638 _69706 _69705 _69707)). Qed.
Lemma lem5331642 (_69704 : int) (_69707 : int) : (term315 _69707 _69704) = (term392 _69704 _69707).
Proof. exact (@lem1988287 (real_of_int _69704) (term307 _69707)). Qed.
Lemma lem5331654 (_69704 : int) (_69707 : int) : (term393 _69704 _69707) = (term394 _69704 _69707).
Proof. exact (@lem1982792 (real_of_int _69704) (term307 _69707)). Qed.
Lemma lem5331655 (_69707 : int) : (term395 _69707) = (term396 _69707).
Proof. exact (@lem1982781 (real_of_int _69707) term355 term305). Qed.
Lemma lem5331657 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331658 : term305 = term397.
Proof. exact (@lem5331657 term157). Qed.
Lemma lem5331660 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331661 : term355 = term356.
Proof. exact (@lem5331660 term157). Qed.
Lemma lem5331662 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331663 : term357 = term358.
Proof. exact (MK_COMB (@lem5331662) (@lem5331661)). Qed.
Lemma lem5331664 : term398 = term399.
Proof. exact (MK_COMB (@lem5331663) (@lem5331658)). Qed.
Lemma lem5331665 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331667 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331668 : term364 = term365.
Proof. exact (@lem5331667 term157 term157). Qed.
Lemma lem5331669 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331670 : term367 = term157.
Proof. exact (EQ_MP (@lem5331669) (@lem940073)). Qed.
Lemma lem5331671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331672 : term365 = term305.
Proof. exact (MK_COMB (@lem5331671) (@lem5331670)). Qed.
Lemma lem5331673 : term364 = term305.
Proof. exact (TRANS (@lem5331668) (@lem5331672)). Qed.
Lemma lem5331675 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331676 : term398 = term403.
Proof. exact (@lem5331675 term157 term157). Qed.
Lemma lem5331677 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331678 : term367 = term157.
Proof. exact (EQ_MP (@lem5331677) (@lem940073)). Qed.
Lemma lem5331679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331680 : term365 = term305.
Proof. exact (MK_COMB (@lem5331679) (@lem5331678)). Qed.
Lemma lem5331681 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331682 : term403 = term355.
Proof. exact (MK_COMB (@lem5331681) (@lem5331680)). Qed.
Lemma lem5331683 : term398 = term355.
Proof. exact (TRANS (@lem5331676) (@lem5331682)). Qed.
Lemma lem5331684 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331685 : term404 = term405.
Proof. exact (MK_COMB (@lem5331684) (@lem5331683)). Qed.
Lemma lem5331686 : term400 = term356.
Proof. exact (MK_COMB (@lem5331685) (@lem5331673)). Qed.
Lemma lem5331687 : term399 = term356.
Proof. exact (TRANS (@lem5331665) (@lem5331686)). Qed.
Lemma lem5331688 : term398 = term356.
Proof. exact (TRANS (@lem5331664) (@lem5331687)). Qed.
Lemma lem5331690 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331691 : term356 = term355.
Proof. exact (@lem5331690 term355). Qed.
Lemma lem5331692 : term398 = term355.
Proof. exact (TRANS (@lem5331688) (@lem5331691)). Qed.
Lemma lem5331695 (_69707 : int) : (term406 _69707) = (term406 _69707).
Proof. exact (eq_refl (term406 _69707)). Qed.
Lemma lem5331696 (_69707 : int) : (term396 _69707) = (term407 _69707).
Proof. exact (MK_COMB (@lem5331695 _69707) (@lem5331692)). Qed.
Lemma lem5331697 (_69707 : int) : (term395 _69707) = (term407 _69707).
Proof. exact (TRANS (@lem5331655 _69707) (@lem5331696 _69707)). Qed.
Lemma lem5331698 (_69704 : int) : (term306 _69704) = (term306 _69704).
Proof. exact (eq_refl (term306 _69704)). Qed.
Lemma lem5331701 (_69704 : int) (_69707 : int) : (term394 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (MK_COMB (@lem5331698 _69704) (@lem5331697 _69707)). Qed.
Lemma lem5331703 (_69704 : int) (_69707 : int) : (term393 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (TRANS (@lem5331654 _69704 _69707) (@lem5331701 _69704 _69707)). Qed.
Lemma lem5331704 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331705 (_69704 : int) (_69707 : int) : (term409 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5331704) (@lem5331703 _69704 _69707)). Qed.
Lemma lem5331706 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331707 (_69704 : int) (_69707 : int) : (term392 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5331705 _69704 _69707) (@lem5331706)). Qed.
Lemma lem5331708 (_69704 : int) (_69707 : int) : (term315 _69707 _69704) = (term411 _69704 _69707).
Proof. exact (TRANS (@lem5331642 _69704 _69707) (@lem5331707 _69704 _69707)). Qed.
Lemma lem5331709 (_69707 : int) (_69705 : int) : (term315 _69705 _69707) = (term392 _69707 _69705).
Proof. exact (@lem1988287 (real_of_int _69707) (term307 _69705)). Qed.
Lemma lem5331721 (_69707 : int) (_69705 : int) : (term393 _69707 _69705) = (term394 _69707 _69705).
Proof. exact (@lem1982792 (real_of_int _69707) (term307 _69705)). Qed.
Lemma lem5331722 (_69705 : int) : (term395 _69705) = (term396 _69705).
Proof. exact (@lem1982781 (real_of_int _69705) term355 term305). Qed.
Lemma lem5331724 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5331725 : term305 = term397.
Proof. exact (@lem5331724 term157). Qed.
Lemma lem5331727 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5331728 : term355 = term356.
Proof. exact (@lem5331727 term157). Qed.
Lemma lem5331729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5331730 : term357 = term358.
Proof. exact (MK_COMB (@lem5331729) (@lem5331728)). Qed.
Lemma lem5331731 : term398 = term399.
Proof. exact (MK_COMB (@lem5331730) (@lem5331725)). Qed.
Lemma lem5331732 : term399 = term400.
Proof. exact (@lem1981613 term355 term305 term305 term305). Qed.
Lemma lem5331734 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5331735 : term364 = term365.
Proof. exact (@lem5331734 term157 term157). Qed.
Lemma lem5331736 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331737 : term367 = term157.
Proof. exact (EQ_MP (@lem5331736) (@lem940073)). Qed.
Lemma lem5331738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331739 : term365 = term305.
Proof. exact (MK_COMB (@lem5331738) (@lem5331737)). Qed.
Lemma lem5331740 : term364 = term305.
Proof. exact (TRANS (@lem5331735) (@lem5331739)). Qed.
Lemma lem5331742 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5331743 : term398 = term403.
Proof. exact (@lem5331742 term157 term157). Qed.
Lemma lem5331744 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5331745 : term367 = term157.
Proof. exact (EQ_MP (@lem5331744) (@lem940073)). Qed.
Lemma lem5331746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5331747 : term365 = term305.
Proof. exact (MK_COMB (@lem5331746) (@lem5331745)). Qed.
Lemma lem5331748 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5331749 : term403 = term355.
Proof. exact (MK_COMB (@lem5331748) (@lem5331747)). Qed.
Lemma lem5331750 : term398 = term355.
Proof. exact (TRANS (@lem5331743) (@lem5331749)). Qed.
Lemma lem5331751 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5331752 : term404 = term405.
Proof. exact (MK_COMB (@lem5331751) (@lem5331750)). Qed.
Lemma lem5331753 : term400 = term356.
Proof. exact (MK_COMB (@lem5331752) (@lem5331740)). Qed.
Lemma lem5331754 : term399 = term356.
Proof. exact (TRANS (@lem5331732) (@lem5331753)). Qed.
Lemma lem5331755 : term398 = term356.
Proof. exact (TRANS (@lem5331731) (@lem5331754)). Qed.
Lemma lem5331757 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5331758 : term356 = term355.
Proof. exact (@lem5331757 term355). Qed.
Lemma lem5331759 : term398 = term355.
Proof. exact (TRANS (@lem5331755) (@lem5331758)). Qed.
Lemma lem5331762 (_69705 : int) : (term406 _69705) = (term406 _69705).
Proof. exact (eq_refl (term406 _69705)). Qed.
Lemma lem5331763 (_69705 : int) : (term396 _69705) = (term407 _69705).
Proof. exact (MK_COMB (@lem5331762 _69705) (@lem5331759)). Qed.
Lemma lem5331764 (_69705 : int) : (term395 _69705) = (term407 _69705).
Proof. exact (TRANS (@lem5331722 _69705) (@lem5331763 _69705)). Qed.
Lemma lem5331765 (_69707 : int) : (term306 _69707) = (term306 _69707).
Proof. exact (eq_refl (term306 _69707)). Qed.
Lemma lem5331766 (_69707 : int) (_69705 : int) : (term394 _69707 _69705) = (term408 _69707 _69705).
Proof. exact (MK_COMB (@lem5331765 _69707) (@lem5331764 _69705)). Qed.
Lemma lem5331771 (_69705 : int) (_69707 : int) : (term408 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (@lem1982757 (term380 _69705) (real_of_int _69707) term355). Qed.
Lemma lem5331772 (_69705 : int) (_69707 : int) : (term394 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (TRANS (@lem5331766 _69707 _69705) (@lem5331771 _69705 _69707)). Qed.
Lemma lem5331774 (_69705 : int) (_69707 : int) : (term393 _69707 _69705) = (term412 _69705 _69707).
Proof. exact (TRANS (@lem5331721 _69707 _69705) (@lem5331772 _69705 _69707)). Qed.
Lemma lem5331775 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5331776 (_69705 : int) (_69707 : int) : (term409 _69707 _69705) = (term413 _69705 _69707).
Proof. exact (MK_COMB (@lem5331775) (@lem5331774 _69705 _69707)). Qed.
Lemma lem5331777 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5331778 (_69705 : int) (_69707 : int) : (term392 _69707 _69705) = (term414 _69705 _69707).
Proof. exact (MK_COMB (@lem5331776 _69705 _69707) (@lem5331777)). Qed.
Lemma lem5331779 (_69705 : int) (_69707 : int) : (term315 _69705 _69707) = (term414 _69705 _69707).
Proof. exact (TRANS (@lem5331709 _69707 _69705) (@lem5331778 _69705 _69707)). Qed.
Lemma lem5331780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331781 (_69704 : int) (_69707 : int) : (term317 _69707 _69704) = (term415 _69704 _69707).
Proof. exact (MK_COMB (@lem5331780) (@lem5331708 _69704 _69707)). Qed.
Lemma lem5331782 (_69704 : int) (_69705 : int) (_69707 : int) : (term318 _69704 _69705 _69707) = (term416 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331781 _69704 _69707) (@lem5331779 _69705 _69707)). Qed.
Lemma lem5331783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331784 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term335 _69704 _69706 _69707 _69705) = (term463 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331783) (@lem5331641 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331785 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term336 _69706 _69704 _69705 _69707) = (term464 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331784 _69704 _69706 _69705 _69707) (@lem5331782 _69704 _69705 _69707)). Qed.
Lemma lem5331786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331787 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term337 _69706 _69704 _69707 _69705) = (term465 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331786) (@lem5331504 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331788 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term338 _69706 _69704 _69705 _69707) = (term466 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331787 _69706 _69704 _69705 _69707) (@lem5331785 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331790 (_69704 : int) (_69705 : int) (_69706 : int) : (term339 _69704 _69706 _69705) = (term467 _69704 _69705 _69706).
Proof. exact (MK_COMB (@lem5331789) (@lem5331062 _69704 _69705 _69706)). Qed.
Lemma lem5331791 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term340 _69706 _69704 _69705 _69707) = (term468 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331790 _69704 _69705 _69706) (@lem5331788 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331793 (_69707 : int) : (term341 _69707) = (term469 _69707).
Proof. exact (MK_COMB (@lem5331792) (@lem5331015 _69707)). Qed.
Lemma lem5331794 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term342 _69706 _69704 _69705 _69707) = (term470 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331793 _69707) (@lem5331791 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331796 (_69706 : int) : (term341 _69706) = (term469 _69706).
Proof. exact (MK_COMB (@lem5331795) (@lem5330967 _69706)). Qed.
Lemma lem5331797 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term343 _69706 _69704 _69705 _69707) = (term471 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331796 _69706) (@lem5331794 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331799 (_69705 : int) : (term341 _69705) = (term469 _69705).
Proof. exact (MK_COMB (@lem5331798) (@lem5330919 _69705)). Qed.
Lemma lem5331800 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term344 _69706 _69704 _69705 _69707) = (term472 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331799 _69705) (@lem5331797 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331802 (_69704 : int) : (term341 _69704) = (term469 _69704).
Proof. exact (MK_COMB (@lem5331801) (@lem5330871 _69704)). Qed.
Lemma lem5331803 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term345 _69706 _69704 _69705 _69707) = (term473 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331802 _69704) (@lem5331800 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331810 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term347 _69706 _69704 _69705 _69707) = (term473 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5330823 _69706 _69704 _69705 _69707) (@lem5331803 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331836 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term464 _69706 _69704 _69705 _69707) = (term474 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term411 _69704 _69707) (term462 _69704 _69706 _69705 _69707) (term414 _69705 _69707)). Qed.
Lemma lem5331843 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term475 _69704 _69706 _69705 _69707) = (term476 _69704 _69706 _69705 _69707).
Proof. exact (@lem19367 (term456 _69704 _69706 _69707) (term460 _69706 _69705 _69707) (term414 _69705 _69707)). Qed.
Lemma lem5331850 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term477 _69706 _69705 _69704 _69707) = (term478 _69706 _69705 _69704 _69707).
Proof. exact (@lem19367 (term456 _69704 _69706 _69707) (term460 _69706 _69705 _69707) (term411 _69704 _69707)). Qed.
Lemma lem5331851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331852 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term479 _69706 _69705 _69704 _69707) = (term480 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5331851) (@lem5331850 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5331853 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term474 _69704 _69706 _69705 _69707) = (term481 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331852 _69706 _69705 _69704 _69707) (@lem5331843 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331855 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term464 _69706 _69704 _69705 _69707) = (term481 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331836 _69704 _69706 _69705 _69707) (@lem5331853 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331862 (_69704 : int) (_69705 : int) (_69707 : int) : (term456 _69704 _69705 _69707) = (term456 _69704 _69705 _69707).
Proof. exact (eq_refl (term456 _69704 _69705 _69707)). Qed.
Lemma lem5331876 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term451 _69704 _69706 _69705 _69707) = (term482 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term389 _69706 _69707) (term416 _69704 _69706 _69707) (term414 _69705 _69707)). Qed.
Lemma lem5331883 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term483 _69704 _69706 _69705 _69707) = (term484 _69704 _69706 _69705 _69707).
Proof. exact (@lem19367 (term411 _69704 _69707) (term414 _69706 _69707) (term414 _69705 _69707)). Qed.
Lemma lem5331890 (_69704 : int) (_69706 : int) (_69707 : int) : (term485 _69704 _69706 _69707) = (term486 _69704 _69706 _69707).
Proof. exact (@lem19367 (term411 _69704 _69707) (term414 _69706 _69707) (term389 _69706 _69707)). Qed.
Lemma lem5331891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331892 (_69704 : int) (_69706 : int) (_69707 : int) : (term487 _69704 _69706 _69707) = (term488 _69704 _69706 _69707).
Proof. exact (MK_COMB (@lem5331891) (@lem5331890 _69704 _69706 _69707)). Qed.
Lemma lem5331893 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term482 _69704 _69706 _69705 _69707) = (term489 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331892 _69704 _69706 _69707) (@lem5331883 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331895 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term451 _69704 _69706 _69705 _69707) = (term489 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331876 _69704 _69706 _69705 _69707) (@lem5331893 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5331897 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term457 _69704 _69706 _69705 _69707) = (term490 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331896) (@lem5331895 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331898 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term458 _69706 _69704 _69705 _69707) = (term491 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331897 _69704 _69706 _69705 _69707) (@lem5331862 _69704 _69705 _69707)). Qed.
Lemma lem5331899 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term491 _69706 _69704 _69705 _69707) = (term492 _69706 _69704 _69705 _69707).
Proof. exact (@lem19367 (term486 _69704 _69706 _69707) (term484 _69704 _69706 _69705 _69707) (term456 _69704 _69705 _69707)). Qed.
Lemma lem5331906 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term493 _69706 _69704 _69705 _69707) = (term494 _69706 _69704 _69705 _69707).
Proof. exact (@lem19367 (term495 _69704 _69705 _69707) (term496 _69706 _69705 _69707) (term456 _69704 _69705 _69707)). Qed.
Lemma lem5331913 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term497 _69706 _69704 _69705 _69707) = (term498 _69706 _69704 _69705 _69707).
Proof. exact (@lem19367 (term499 _69704 _69706 _69707) (term500 _69706 _69707) (term456 _69704 _69705 _69707)). Qed.
Lemma lem5331914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331915 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term501 _69706 _69704 _69705 _69707) = (term502 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331914) (@lem5331913 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331916 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term492 _69706 _69704 _69705 _69707) = (term503 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331915 _69706 _69704 _69705 _69707) (@lem5331906 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331917 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term491 _69706 _69704 _69705 _69707) = (term503 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5331899 _69706 _69704 _69705 _69707) (@lem5331916 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331918 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term458 _69706 _69704 _69705 _69707) = (term503 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5331898 _69706 _69704 _69705 _69707) (@lem5331917 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331920 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term465 _69706 _69704 _69705 _69707) = (term504 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331919) (@lem5331918 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331921 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term466 _69706 _69704 _69705 _69707) = (term505 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331920 _69706 _69704 _69705 _69707) (@lem5331855 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331930 (_69704 : int) (_69705 : int) (_69706 : int) : (term467 _69704 _69705 _69706) = (term467 _69704 _69705 _69706).
Proof. exact (eq_refl (term467 _69704 _69705 _69706)). Qed.
Lemma lem5331931 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term468 _69706 _69704 _69705 _69707) = (term506 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331930 _69704 _69705 _69706) (@lem5331921 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331932 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term506 _69704 _69706 _69705 _69707) = (term507 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term503 _69706 _69704 _69705 _69707) (term391 _69704 _69705 _69706) (term481 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331933 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term508 _69704 _69706 _69705 _69707) = (term509 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term478 _69706 _69705 _69704 _69707) (term391 _69704 _69705 _69706) (term476 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331940 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term510 _69704 _69706 _69705 _69707) = (term511 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term512 _69704 _69706 _69705 _69707) (term391 _69704 _69705 _69706) (term513 _69706 _69705 _69707)). Qed.
Lemma lem5331947 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term514 _69706 _69705 _69704 _69707) = (term515 _69706 _69705 _69704 _69707).
Proof. exact (@lem19158 (term516 _69706 _69704 _69707) (term391 _69704 _69705 _69706) (term517 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5331948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331949 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term518 _69706 _69705 _69704 _69707) = (term519 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5331948) (@lem5331947 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5331950 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term509 _69704 _69706 _69705 _69707) = (term520 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331949 _69706 _69705 _69704 _69707) (@lem5331940 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331951 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term508 _69704 _69706 _69705 _69707) = (term520 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331933 _69704 _69706 _69705 _69707) (@lem5331950 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331952 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term521 _69706 _69704 _69705 _69707) = (term522 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term498 _69706 _69704 _69705 _69707) (term391 _69704 _69705 _69706) (term494 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331959 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term523 _69706 _69704 _69705 _69707) = (term524 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term525 _69704 _69705 _69707) (term391 _69704 _69705 _69706) (term526 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331966 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term527 _69706 _69704 _69705 _69707) = (term528 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term529 _69706 _69704 _69705 _69707) (term391 _69704 _69705 _69706) (term530 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331968 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term531 _69706 _69704 _69705 _69707) = (term532 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331967) (@lem5331966 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331969 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term522 _69706 _69704 _69705 _69707) = (term533 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331968 _69706 _69704 _69705 _69707) (@lem5331959 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331970 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term521 _69706 _69704 _69705 _69707) = (term533 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5331952 _69706 _69704 _69705 _69707) (@lem5331969 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331972 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term534 _69706 _69704 _69705 _69707) = (term535 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5331971) (@lem5331970 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5331973 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term507 _69704 _69706 _69705 _69707) = (term536 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331972 _69706 _69704 _69705 _69707) (@lem5331951 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331974 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term506 _69704 _69706 _69705 _69707) = (term536 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331932 _69704 _69706 _69705 _69707) (@lem5331973 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331975 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term468 _69706 _69704 _69705 _69707) = (term536 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331931 _69704 _69706 _69705 _69707) (@lem5331974 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331978 (_69707 : int) : (term469 _69707) = (term469 _69707).
Proof. exact (eq_refl (term469 _69707)). Qed.
Lemma lem5331979 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term470 _69706 _69704 _69705 _69707) = (term537 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331978 _69707) (@lem5331975 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331980 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term537 _69704 _69706 _69705 _69707) = (term538 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term533 _69706 _69704 _69705 _69707) (term375 _69707) (term520 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331981 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term539 _69704 _69706 _69705 _69707) = (term540 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term515 _69706 _69705 _69704 _69707) (term375 _69707) (term511 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331988 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term541 _69704 _69706 _69705 _69707) = (term542 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term543 _69704 _69706 _69705 _69707) (term375 _69707) (term544 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331995 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term545 _69706 _69705 _69704 _69707) = (term546 _69706 _69705 _69704 _69707).
Proof. exact (@lem19158 (term547 _69705 _69706 _69704 _69707) (term375 _69707) (term548 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5331996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5331997 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term549 _69706 _69705 _69704 _69707) = (term550 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5331996) (@lem5331995 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5331998 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term540 _69704 _69706 _69705 _69707) = (term551 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5331997 _69706 _69705 _69704 _69707) (@lem5331988 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5331999 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term539 _69704 _69706 _69705 _69707) = (term551 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331981 _69704 _69706 _69705 _69707) (@lem5331998 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332000 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term552 _69706 _69704 _69705 _69707) = (term553 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term528 _69706 _69704 _69705 _69707) (term375 _69707) (term524 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332007 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term554 _69706 _69704 _69705 _69707) = (term555 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term556 _69706 _69704 _69705 _69707) (term375 _69707) (term557 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332014 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term558 _69706 _69704 _69705 _69707) = (term559 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term560 _69706 _69704 _69705 _69707) (term375 _69707) (term561 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332016 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term562 _69706 _69704 _69705 _69707) = (term563 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332015) (@lem5332014 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332017 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term553 _69706 _69704 _69705 _69707) = (term564 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332016 _69706 _69704 _69705 _69707) (@lem5332007 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332018 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term552 _69706 _69704 _69705 _69707) = (term564 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5332000 _69706 _69704 _69705 _69707) (@lem5332017 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332020 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term565 _69706 _69704 _69705 _69707) = (term566 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332019) (@lem5332018 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332021 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term538 _69704 _69706 _69705 _69707) = (term567 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332020 _69706 _69704 _69705 _69707) (@lem5331999 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332022 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term537 _69704 _69706 _69705 _69707) = (term567 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331980 _69704 _69706 _69705 _69707) (@lem5332021 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332023 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term470 _69706 _69704 _69705 _69707) = (term567 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331979 _69704 _69706 _69705 _69707) (@lem5332022 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332026 (_69706 : int) : (term469 _69706) = (term469 _69706).
Proof. exact (eq_refl (term469 _69706)). Qed.
Lemma lem5332027 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term471 _69706 _69704 _69705 _69707) = (term568 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332026 _69706) (@lem5332023 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332028 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term568 _69704 _69706 _69705 _69707) = (term569 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term564 _69706 _69704 _69705 _69707) (term375 _69706) (term551 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332029 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term570 _69704 _69706 _69705 _69707) = (term571 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term546 _69706 _69705 _69704 _69707) (term375 _69706) (term542 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332036 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term572 _69704 _69706 _69705 _69707) = (term573 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term574 _69704 _69706 _69705 _69707) (term375 _69706) (term575 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332043 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term576 _69706 _69705 _69704 _69707) = (term577 _69706 _69705 _69704 _69707).
Proof. exact (@lem19158 (term578 _69705 _69706 _69704 _69707) (term375 _69706) (term579 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332045 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term580 _69706 _69705 _69704 _69707) = (term581 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5332044) (@lem5332043 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332046 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term571 _69704 _69706 _69705 _69707) = (term582 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332045 _69706 _69705 _69704 _69707) (@lem5332036 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332047 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term570 _69704 _69706 _69705 _69707) = (term582 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332029 _69704 _69706 _69705 _69707) (@lem5332046 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332048 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term583 _69706 _69704 _69705 _69707) = (term584 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term559 _69706 _69704 _69705 _69707) (term375 _69706) (term555 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332055 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term585 _69706 _69704 _69705 _69707) = (term586 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term587 _69706 _69704 _69705 _69707) (term375 _69706) (term588 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332062 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term589 _69706 _69704 _69705 _69707) = (term590 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term591 _69706 _69704 _69705 _69707) (term375 _69706) (term592 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332064 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term593 _69706 _69704 _69705 _69707) = (term594 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332063) (@lem5332062 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332065 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term584 _69706 _69704 _69705 _69707) = (term595 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332064 _69706 _69704 _69705 _69707) (@lem5332055 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332066 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term583 _69706 _69704 _69705 _69707) = (term595 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5332048 _69706 _69704 _69705 _69707) (@lem5332065 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332068 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term596 _69706 _69704 _69705 _69707) = (term597 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332067) (@lem5332066 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332069 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term569 _69704 _69706 _69705 _69707) = (term598 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332068 _69706 _69704 _69705 _69707) (@lem5332047 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332070 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term568 _69704 _69706 _69705 _69707) = (term598 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332028 _69704 _69706 _69705 _69707) (@lem5332069 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332071 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term471 _69706 _69704 _69705 _69707) = (term598 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332027 _69704 _69706 _69705 _69707) (@lem5332070 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332074 (_69705 : int) : (term469 _69705) = (term469 _69705).
Proof. exact (eq_refl (term469 _69705)). Qed.
Lemma lem5332075 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term472 _69706 _69704 _69705 _69707) = (term599 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332074 _69705) (@lem5332071 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332076 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term599 _69704 _69706 _69705 _69707) = (term600 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term595 _69706 _69704 _69705 _69707) (term375 _69705) (term582 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332077 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term601 _69704 _69706 _69705 _69707) = (term602 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term577 _69706 _69705 _69704 _69707) (term375 _69705) (term573 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332084 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term603 _69704 _69706 _69705 _69707) = (term604 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term605 _69704 _69706 _69705 _69707) (term375 _69705) (term606 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332091 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term607 _69706 _69705 _69704 _69707) = (term608 _69706 _69705 _69704 _69707).
Proof. exact (@lem19158 (term609 _69705 _69706 _69704 _69707) (term375 _69705) (term610 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332093 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term611 _69706 _69705 _69704 _69707) = (term612 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5332092) (@lem5332091 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332094 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term602 _69704 _69706 _69705 _69707) = (term613 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332093 _69706 _69705 _69704 _69707) (@lem5332084 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332095 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term601 _69704 _69706 _69705 _69707) = (term613 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332077 _69704 _69706 _69705 _69707) (@lem5332094 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332096 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term614 _69706 _69704 _69705 _69707) = (term615 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term590 _69706 _69704 _69705 _69707) (term375 _69705) (term586 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332103 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term616 _69706 _69704 _69705 _69707) = (term617 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term618 _69706 _69704 _69705 _69707) (term375 _69705) (term619 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332110 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term620 _69706 _69704 _69705 _69707) = (term621 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term622 _69706 _69704 _69705 _69707) (term375 _69705) (term623 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332112 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term624 _69706 _69704 _69705 _69707) = (term625 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332111) (@lem5332110 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332113 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term615 _69706 _69704 _69705 _69707) = (term626 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332112 _69706 _69704 _69705 _69707) (@lem5332103 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332114 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term614 _69706 _69704 _69705 _69707) = (term626 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5332096 _69706 _69704 _69705 _69707) (@lem5332113 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332116 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term627 _69706 _69704 _69705 _69707) = (term628 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332115) (@lem5332114 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332117 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term600 _69704 _69706 _69705 _69707) = (term629 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332116 _69706 _69704 _69705 _69707) (@lem5332095 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332118 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term599 _69704 _69706 _69705 _69707) = (term629 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332076 _69704 _69706 _69705 _69707) (@lem5332117 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332119 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term472 _69706 _69704 _69705 _69707) = (term629 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332075 _69704 _69706 _69705 _69707) (@lem5332118 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332122 (_69704 : int) : (term469 _69704) = (term469 _69704).
Proof. exact (eq_refl (term469 _69704)). Qed.
Lemma lem5332123 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term473 _69706 _69704 _69705 _69707) = (term630 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332122 _69704) (@lem5332119 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332124 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term630 _69704 _69706 _69705 _69707) = (term631 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term626 _69706 _69704 _69705 _69707) (term375 _69704) (term613 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332125 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term632 _69704 _69706 _69705 _69707) = (term633 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term608 _69706 _69705 _69704 _69707) (term375 _69704) (term604 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332132 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term634 _69704 _69706 _69705 _69707) = (term635 _69704 _69706 _69705 _69707).
Proof. exact (@lem19158 (term636 _69704 _69706 _69705 _69707) (term375 _69704) (term637 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332139 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term638 _69706 _69705 _69704 _69707) = (term639 _69706 _69705 _69704 _69707).
Proof. exact (@lem19158 (term640 _69705 _69706 _69704 _69707) (term375 _69704) (term641 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332141 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) : (term642 _69706 _69705 _69704 _69707) = (term643 _69706 _69705 _69704 _69707).
Proof. exact (MK_COMB (@lem5332140) (@lem5332139 _69706 _69705 _69704 _69707)). Qed.
Lemma lem5332142 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term633 _69704 _69706 _69705 _69707) = (term644 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332141 _69706 _69705 _69704 _69707) (@lem5332132 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332143 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term632 _69704 _69706 _69705 _69707) = (term644 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332125 _69704 _69706 _69705 _69707) (@lem5332142 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332144 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term645 _69706 _69704 _69705 _69707) = (term646 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term621 _69706 _69704 _69705 _69707) (term375 _69704) (term617 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332151 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term647 _69706 _69704 _69705 _69707) = (term648 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term649 _69706 _69704 _69705 _69707) (term375 _69704) (term650 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332158 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term651 _69706 _69704 _69705 _69707) = (term652 _69706 _69704 _69705 _69707).
Proof. exact (@lem19158 (term653 _69706 _69704 _69705 _69707) (term375 _69704) (term654 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332160 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term655 _69706 _69704 _69705 _69707) = (term656 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332159) (@lem5332158 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332161 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term646 _69706 _69704 _69705 _69707) = (term657 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332160 _69706 _69704 _69705 _69707) (@lem5332151 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332162 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term645 _69706 _69704 _69705 _69707) = (term657 _69706 _69704 _69705 _69707).
Proof. exact (TRANS (@lem5332144 _69706 _69704 _69705 _69707) (@lem5332161 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5332164 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : (term658 _69706 _69704 _69705 _69707) = (term659 _69706 _69704 _69705 _69707).
Proof. exact (MK_COMB (@lem5332163) (@lem5332162 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5332165 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term631 _69704 _69706 _69705 _69707) = (term660 _69704 _69706 _69705 _69707).
Proof. exact (MK_COMB (@lem5332164 _69706 _69704 _69705 _69707) (@lem5332143 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332166 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term630 _69704 _69706 _69705 _69707) = (term660 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332124 _69704 _69706 _69705 _69707) (@lem5332165 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332167 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term473 _69706 _69704 _69705 _69707) = (term660 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5332123 _69704 _69706 _69705 _69707) (@lem5332166 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332168 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) : (term347 _69706 _69704 _69705 _69707) = (term660 _69704 _69706 _69705 _69707).
Proof. exact (TRANS (@lem5331810 _69706 _69704 _69705 _69707) (@lem5332167 _69704 _69706 _69705 _69707)). Qed.
Lemma lem5332214 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term660 _69704 _69706 _69705 _69707) : term660 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5332215 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term657 _69706 _69704 _69705 _69707) : term657 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5332216 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term652 _69706 _69704 _69705 _69707) : term652 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5332217 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term661 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5332218 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term653 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332217 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332220 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term622 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332218 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332222 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term591 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332220 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332224 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term560 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332222 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332226 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term529 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332224 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332230 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term456 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332226 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332231 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term499 _69704 _69706 _69707.
Proof. exact (proj1 (@lem5332226 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332233 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term411 _69704 _69707.
Proof. exact (proj1 (@lem5332231 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332235 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term454 _69704 _69707.
Proof. exact (proj1 (@lem5332230 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332237 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5332238 : term662 = term431.
Proof. exact (@lem5332237 term293 term305). Qed.
Lemma lem5332240 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332241 : term305 = term397.
Proof. exact (@lem5332240 term157). Qed.
Lemma lem5332243 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332244 : term293 = term352.
Proof. exact (@lem5332243 (NUMERAL 0)). Qed.
Lemma lem5332245 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332246 : term663 = term664.
Proof. exact (MK_COMB (@lem5332245) (@lem5332244)). Qed.
Lemma lem5332247 : term431 = term665.
Proof. exact (MK_COMB (@lem5332246) (@lem5332241)). Qed.
Lemma lem5332248 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5332250 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332251 : term431 = term432.
Proof. exact (@lem5332250 (NUMERAL 0) term157). Qed.
Lemma lem5332252 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332253 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332254 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332253 h1) (fun h1 : term432 = True => @lem5332252)). Qed.
Lemma lem5332255 : term432 = True.
Proof. exact (EQ_MP (@lem5332254) (@lem5332252)). Qed.
Lemma lem5332256 : term431 = True.
Proof. exact (TRANS (@lem5332251) (@lem5332255)). Qed.
Lemma lem5332257 : True = term431.
Proof. exact (SYM (@lem5332256)). Qed.
Lemma lem5332258 : term431.
Proof. exact (EQ_MP (@lem5332257) (@lem0)). Qed.
Lemma lem5332259 : term667.
Proof. exact (@lem5332248 (@lem5332258)). Qed.
Lemma lem5332261 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332262 : term431 = term432.
Proof. exact (@lem5332261 (NUMERAL 0) term157). Qed.
Lemma lem5332263 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332264 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332265 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332264 h1) (fun h1 : term432 = True => @lem5332263)). Qed.
Lemma lem5332266 : term432 = True.
Proof. exact (EQ_MP (@lem5332265) (@lem5332263)). Qed.
Lemma lem5332267 : term431 = True.
Proof. exact (TRANS (@lem5332262) (@lem5332266)). Qed.
Lemma lem5332268 : True = term431.
Proof. exact (SYM (@lem5332267)). Qed.
Lemma lem5332269 : term431.
Proof. exact (EQ_MP (@lem5332268) (@lem0)). Qed.
Lemma lem5332270 : term665 = term668.
Proof. exact (@lem5332259 (@lem5332269)). Qed.
Lemma lem5332272 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332273 : term364 = term365.
Proof. exact (@lem5332272 term157 term157). Qed.
Lemma lem5332274 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332275 : term367 = term157.
Proof. exact (EQ_MP (@lem5332274) (@lem940073)). Qed.
Lemma lem5332276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332277 : term365 = term305.
Proof. exact (MK_COMB (@lem5332276) (@lem5332275)). Qed.
Lemma lem5332278 : term364 = term305.
Proof. exact (TRANS (@lem5332273) (@lem5332277)). Qed.
Lemma lem5332280 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332281 : term443 = term293.
Proof. exact (@lem5332280 term157). Qed.
Lemma lem5332282 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332283 : term669 = term663.
Proof. exact (MK_COMB (@lem5332282) (@lem5332281)). Qed.
Lemma lem5332284 : term668 = term431.
Proof. exact (MK_COMB (@lem5332283) (@lem5332278)). Qed.
Lemma lem5332286 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332287 : term431 = term432.
Proof. exact (@lem5332286 (NUMERAL 0) term157). Qed.
Lemma lem5332288 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332289 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332290 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332289 h1) (fun h1 : term432 = True => @lem5332288)). Qed.
Lemma lem5332291 : term432 = True.
Proof. exact (EQ_MP (@lem5332290) (@lem5332288)). Qed.
Lemma lem5332292 : term431 = True.
Proof. exact (TRANS (@lem5332287) (@lem5332291)). Qed.
Lemma lem5332293 : term668 = True.
Proof. exact (TRANS (@lem5332284) (@lem5332292)). Qed.
Lemma lem5332294 : term665 = True.
Proof. exact (TRANS (@lem5332270) (@lem5332293)). Qed.
Lemma lem5332295 : term431 = True.
Proof. exact (TRANS (@lem5332247) (@lem5332294)). Qed.
Lemma lem5332296 : term662 = True.
Proof. exact (TRANS (@lem5332238) (@lem5332295)). Qed.
Lemma lem5332297 : True = term662.
Proof. exact (SYM (@lem5332296)). Qed.
Lemma lem5332298 : term662.
Proof. exact (EQ_MP (@lem5332297) (@lem0)). Qed.
Lemma lem5332299 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term670 _69704 _69707.
Proof. exact (conj (@lem5332298) (@lem5332233 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332301 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5332302 (_69704 : int) (_69707 : int) : term672 _69704 _69707.
Proof. exact (@lem5332301 term305 (term408 _69704 _69707)). Qed.
Lemma lem5332303 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term673 _69704 _69707.
Proof. exact (@lem5332302 _69704 _69707 (@lem5332299 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332304 (_69704 : int) (_69707 : int) : (term674 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (@lem1982733 (term408 _69704 _69707)). Qed.
Lemma lem5332305 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5332306 (_69704 : int) (_69707 : int) : (term675 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5332305) (@lem5332304 _69704 _69707)). Qed.
Lemma lem5332307 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5332308 (_69704 : int) (_69707 : int) : (term673 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5332306 _69704 _69707) (@lem5332307)). Qed.
Lemma lem5332309 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term411 _69704 _69707.
Proof. exact (EQ_MP (@lem5332308 _69704 _69707) (@lem5332303 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332311 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5332312 : term662 = term431.
Proof. exact (@lem5332311 term293 term305). Qed.
Lemma lem5332314 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332315 : term305 = term397.
Proof. exact (@lem5332314 term157). Qed.
Lemma lem5332317 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332318 : term293 = term352.
Proof. exact (@lem5332317 (NUMERAL 0)). Qed.
Lemma lem5332319 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332320 : term663 = term664.
Proof. exact (MK_COMB (@lem5332319) (@lem5332318)). Qed.
Lemma lem5332321 : term431 = term665.
Proof. exact (MK_COMB (@lem5332320) (@lem5332315)). Qed.
Lemma lem5332322 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5332324 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332325 : term431 = term432.
Proof. exact (@lem5332324 (NUMERAL 0) term157). Qed.
Lemma lem5332326 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332327 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332328 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332327 h1) (fun h1 : term432 = True => @lem5332326)). Qed.
Lemma lem5332329 : term432 = True.
Proof. exact (EQ_MP (@lem5332328) (@lem5332326)). Qed.
Lemma lem5332330 : term431 = True.
Proof. exact (TRANS (@lem5332325) (@lem5332329)). Qed.
Lemma lem5332331 : True = term431.
Proof. exact (SYM (@lem5332330)). Qed.
Lemma lem5332332 : term431.
Proof. exact (EQ_MP (@lem5332331) (@lem0)). Qed.
Lemma lem5332333 : term667.
Proof. exact (@lem5332322 (@lem5332332)). Qed.
Lemma lem5332335 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332336 : term431 = term432.
Proof. exact (@lem5332335 (NUMERAL 0) term157). Qed.
Lemma lem5332337 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332338 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332339 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332338 h1) (fun h1 : term432 = True => @lem5332337)). Qed.
Lemma lem5332340 : term432 = True.
Proof. exact (EQ_MP (@lem5332339) (@lem5332337)). Qed.
Lemma lem5332341 : term431 = True.
Proof. exact (TRANS (@lem5332336) (@lem5332340)). Qed.
Lemma lem5332342 : True = term431.
Proof. exact (SYM (@lem5332341)). Qed.
Lemma lem5332343 : term431.
Proof. exact (EQ_MP (@lem5332342) (@lem0)). Qed.
Lemma lem5332344 : term665 = term668.
Proof. exact (@lem5332333 (@lem5332343)). Qed.
Lemma lem5332346 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332347 : term364 = term365.
Proof. exact (@lem5332346 term157 term157). Qed.
Lemma lem5332348 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332349 : term367 = term157.
Proof. exact (EQ_MP (@lem5332348) (@lem940073)). Qed.
Lemma lem5332350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332351 : term365 = term305.
Proof. exact (MK_COMB (@lem5332350) (@lem5332349)). Qed.
Lemma lem5332352 : term364 = term305.
Proof. exact (TRANS (@lem5332347) (@lem5332351)). Qed.
Lemma lem5332354 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332355 : term443 = term293.
Proof. exact (@lem5332354 term157). Qed.
Lemma lem5332356 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332357 : term669 = term663.
Proof. exact (MK_COMB (@lem5332356) (@lem5332355)). Qed.
Lemma lem5332358 : term668 = term431.
Proof. exact (MK_COMB (@lem5332357) (@lem5332352)). Qed.
Lemma lem5332360 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332361 : term431 = term432.
Proof. exact (@lem5332360 (NUMERAL 0) term157). Qed.
Lemma lem5332362 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332363 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332364 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332363 h1) (fun h1 : term432 = True => @lem5332362)). Qed.
Lemma lem5332365 : term432 = True.
Proof. exact (EQ_MP (@lem5332364) (@lem5332362)). Qed.
Lemma lem5332366 : term431 = True.
Proof. exact (TRANS (@lem5332361) (@lem5332365)). Qed.
Lemma lem5332367 : term668 = True.
Proof. exact (TRANS (@lem5332358) (@lem5332366)). Qed.
Lemma lem5332368 : term665 = True.
Proof. exact (TRANS (@lem5332344) (@lem5332367)). Qed.
Lemma lem5332369 : term431 = True.
Proof. exact (TRANS (@lem5332321) (@lem5332368)). Qed.
Lemma lem5332370 : term662 = True.
Proof. exact (TRANS (@lem5332312) (@lem5332369)). Qed.
Lemma lem5332371 : True = term662.
Proof. exact (SYM (@lem5332370)). Qed.
Lemma lem5332372 : term662.
Proof. exact (EQ_MP (@lem5332371) (@lem0)). Qed.
Lemma lem5332373 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term676 _69704 _69707.
Proof. exact (conj (@lem5332372) (@lem5332235 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332375 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5332376 (_69704 : int) (_69707 : int) : term677 _69704 _69707.
Proof. exact (@lem5332375 term305 (term452 _69704 _69707)). Qed.
Lemma lem5332377 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term678 _69704 _69707.
Proof. exact (@lem5332376 _69704 _69707 (@lem5332373 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332378 (_69704 : int) (_69707 : int) : (term679 _69704 _69707) = (term452 _69704 _69707).
Proof. exact (@lem1982733 (term452 _69704 _69707)). Qed.
Lemma lem5332379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5332380 (_69704 : int) (_69707 : int) : (term680 _69704 _69707) = (term453 _69704 _69707).
Proof. exact (MK_COMB (@lem5332379) (@lem5332378 _69704 _69707)). Qed.
Lemma lem5332381 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5332382 (_69704 : int) (_69707 : int) : (term678 _69704 _69707) = (term454 _69704 _69707).
Proof. exact (MK_COMB (@lem5332380 _69704 _69707) (@lem5332381)). Qed.
Lemma lem5332383 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term454 _69704 _69707.
Proof. exact (EQ_MP (@lem5332382 _69704 _69707) (@lem5332377 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332384 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term681 _69704 _69707.
Proof. exact (conj (@lem5332383 _69706 _69704 _69705 _69707 h1) (@lem5332309 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332386 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5332387 (_69704 : int) (_69707 : int) : term683 _69704 _69707.
Proof. exact (@lem5332386 (term452 _69704 _69707) (term408 _69704 _69707)). Qed.
Lemma lem5332388 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term684 _69704 _69707.
Proof. exact (@lem5332387 _69704 _69707 (@lem5332384 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332389 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = (term686 _69704 _69707).
Proof. exact (@lem1982753 (term380 _69704) (real_of_int _69704) (real_of_int _69707) (term407 _69707)). Qed.
Lemma lem5332390 (_69704 : int) : (term687 _69704) = (term688 _69704).
Proof. exact (@lem1982713 term355 (real_of_int _69704)). Qed.
Lemma lem5332392 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332393 : term305 = term397.
Proof. exact (@lem5332392 term157). Qed.
Lemma lem5332395 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5332396 : term355 = term356.
Proof. exact (@lem5332395 term157). Qed.
Lemma lem5332397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332398 : term689 = term690.
Proof. exact (MK_COMB (@lem5332397) (@lem5332396)). Qed.
Lemma lem5332399 : term691 = term692.
Proof. exact (MK_COMB (@lem5332398) (@lem5332393)). Qed.
Lemma lem5332400 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5332402 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332403 : term431 = term432.
Proof. exact (@lem5332402 (NUMERAL 0) term157). Qed.
Lemma lem5332404 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332405 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332406 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332405 h1) (fun h1 : term432 = True => @lem5332404)). Qed.
Lemma lem5332407 : term432 = True.
Proof. exact (EQ_MP (@lem5332406) (@lem5332404)). Qed.
Lemma lem5332408 : term431 = True.
Proof. exact (TRANS (@lem5332403) (@lem5332407)). Qed.
Lemma lem5332409 : True = term431.
Proof. exact (SYM (@lem5332408)). Qed.
Lemma lem5332410 : term431.
Proof. exact (EQ_MP (@lem5332409) (@lem0)). Qed.
Lemma lem5332411 : term694.
Proof. exact (@lem5332400 (@lem5332410)). Qed.
Lemma lem5332413 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332414 : term431 = term432.
Proof. exact (@lem5332413 (NUMERAL 0) term157). Qed.
Lemma lem5332415 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332416 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332417 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332416 h1) (fun h1 : term432 = True => @lem5332415)). Qed.
Lemma lem5332418 : term432 = True.
Proof. exact (EQ_MP (@lem5332417) (@lem5332415)). Qed.
Lemma lem5332419 : term431 = True.
Proof. exact (TRANS (@lem5332414) (@lem5332418)). Qed.
Lemma lem5332420 : True = term431.
Proof. exact (SYM (@lem5332419)). Qed.
Lemma lem5332421 : term431.
Proof. exact (EQ_MP (@lem5332420) (@lem0)). Qed.
Lemma lem5332422 : term695.
Proof. exact (@lem5332411 (@lem5332421)). Qed.
Lemma lem5332424 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332425 : term431 = term432.
Proof. exact (@lem5332424 (NUMERAL 0) term157). Qed.
Lemma lem5332426 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332427 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332428 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332427 h1) (fun h1 : term432 = True => @lem5332426)). Qed.
Lemma lem5332429 : term432 = True.
Proof. exact (EQ_MP (@lem5332428) (@lem5332426)). Qed.
Lemma lem5332430 : term431 = True.
Proof. exact (TRANS (@lem5332425) (@lem5332429)). Qed.
Lemma lem5332431 : True = term431.
Proof. exact (SYM (@lem5332430)). Qed.
Lemma lem5332432 : term431.
Proof. exact (EQ_MP (@lem5332431) (@lem0)). Qed.
Lemma lem5332433 : term696.
Proof. exact (@lem5332422 (@lem5332432)). Qed.
Lemma lem5332435 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332436 : term364 = term365.
Proof. exact (@lem5332435 term157 term157). Qed.
Lemma lem5332437 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332438 : term367 = term157.
Proof. exact (EQ_MP (@lem5332437) (@lem940073)). Qed.
Lemma lem5332439 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332440 : term365 = term305.
Proof. exact (MK_COMB (@lem5332439) (@lem5332438)). Qed.
Lemma lem5332441 : term364 = term305.
Proof. exact (TRANS (@lem5332436) (@lem5332440)). Qed.
Lemma lem5332443 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5332444 : term398 = term403.
Proof. exact (@lem5332443 term157 term157). Qed.
Lemma lem5332445 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332446 : term367 = term157.
Proof. exact (EQ_MP (@lem5332445) (@lem940073)). Qed.
Lemma lem5332447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332448 : term365 = term305.
Proof. exact (MK_COMB (@lem5332447) (@lem5332446)). Qed.
Lemma lem5332449 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5332450 : term403 = term355.
Proof. exact (MK_COMB (@lem5332449) (@lem5332448)). Qed.
Lemma lem5332451 : term398 = term355.
Proof. exact (TRANS (@lem5332444) (@lem5332450)). Qed.
Lemma lem5332452 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332453 : term697 = term689.
Proof. exact (MK_COMB (@lem5332452) (@lem5332451)). Qed.
Lemma lem5332454 : term698 = term691.
Proof. exact (MK_COMB (@lem5332453) (@lem5332441)). Qed.
Lemma lem5332456 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5332457 : term691 = term293.
Proof. exact (@lem5332456 term157). Qed.
Lemma lem5332458 : term698 = term293.
Proof. exact (TRANS (@lem5332454) (@lem5332457)). Qed.
Lemma lem5332459 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332460 : term700 = term441.
Proof. exact (MK_COMB (@lem5332459) (@lem5332458)). Qed.
Lemma lem5332461 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5332462 : term701 = term443.
Proof. exact (MK_COMB (@lem5332460) (@lem5332461)). Qed.
Lemma lem5332464 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332465 : term443 = term293.
Proof. exact (@lem5332464 term157). Qed.
Lemma lem5332466 : term701 = term293.
Proof. exact (TRANS (@lem5332462) (@lem5332465)). Qed.
Lemma lem5332468 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332469 : term364 = term365.
Proof. exact (@lem5332468 term157 term157). Qed.
Lemma lem5332470 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332471 : term367 = term157.
Proof. exact (EQ_MP (@lem5332470) (@lem940073)). Qed.
Lemma lem5332472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332473 : term365 = term305.
Proof. exact (MK_COMB (@lem5332472) (@lem5332471)). Qed.
Lemma lem5332474 : term364 = term305.
Proof. exact (TRANS (@lem5332469) (@lem5332473)). Qed.
Lemma lem5332475 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5332476 : term445 = term443.
Proof. exact (MK_COMB (@lem5332475) (@lem5332474)). Qed.
Lemma lem5332478 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332479 : term443 = term293.
Proof. exact (@lem5332478 term157). Qed.
Lemma lem5332480 : term445 = term293.
Proof. exact (TRANS (@lem5332476) (@lem5332479)). Qed.
Lemma lem5332481 : term293 = term445.
Proof. exact (SYM (@lem5332480)). Qed.
Lemma lem5332482 : term701 = term445.
Proof. exact (TRANS (@lem5332466) (@lem5332481)). Qed.
Lemma lem5332483 : term692 = term352.
Proof. exact (@lem5332433 (@lem5332482)). Qed.
Lemma lem5332484 : term691 = term352.
Proof. exact (TRANS (@lem5332399) (@lem5332483)). Qed.
Lemma lem5332486 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5332487 : term352 = term293.
Proof. exact (@lem5332486 term293). Qed.
Lemma lem5332488 : term691 = term293.
Proof. exact (TRANS (@lem5332484) (@lem5332487)). Qed.
Lemma lem5332489 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332490 : term702 = term441.
Proof. exact (MK_COMB (@lem5332489) (@lem5332488)). Qed.
Lemma lem5332491 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5332492 (_69704 : int) : (term688 _69704) = (term703 _69704).
Proof. exact (MK_COMB (@lem5332490) (@lem5332491 _69704)). Qed.
Lemma lem5332493 (_69704 : int) : (term687 _69704) = (term703 _69704).
Proof. exact (TRANS (@lem5332390 _69704) (@lem5332492 _69704)). Qed.
Lemma lem5332494 (_69704 : int) : (term703 _69704) = term293.
Proof. exact (@lem1982719 (real_of_int _69704)). Qed.
Lemma lem5332495 (_69704 : int) : (term687 _69704) = term293.
Proof. exact (TRANS (@lem5332493 _69704) (@lem5332494 _69704)). Qed.
Lemma lem5332496 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332497 (_69704 : int) : (term704 _69704) = term705.
Proof. exact (MK_COMB (@lem5332496) (@lem5332495 _69704)). Qed.
Lemma lem5332498 (_69707 : int) : (term706 _69707) = (term707 _69707).
Proof. exact (@lem1982763 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5332499 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5332501 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332502 : term305 = term397.
Proof. exact (@lem5332501 term157). Qed.
Lemma lem5332504 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5332505 : term355 = term356.
Proof. exact (@lem5332504 term157). Qed.
Lemma lem5332506 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332507 : term689 = term690.
Proof. exact (MK_COMB (@lem5332506) (@lem5332505)). Qed.
Lemma lem5332508 : term691 = term692.
Proof. exact (MK_COMB (@lem5332507) (@lem5332502)). Qed.
Lemma lem5332509 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5332511 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332512 : term431 = term432.
Proof. exact (@lem5332511 (NUMERAL 0) term157). Qed.
Lemma lem5332513 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332514 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332515 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332514 h1) (fun h1 : term432 = True => @lem5332513)). Qed.
Lemma lem5332516 : term432 = True.
Proof. exact (EQ_MP (@lem5332515) (@lem5332513)). Qed.
Lemma lem5332517 : term431 = True.
Proof. exact (TRANS (@lem5332512) (@lem5332516)). Qed.
Lemma lem5332518 : True = term431.
Proof. exact (SYM (@lem5332517)). Qed.
Lemma lem5332519 : term431.
Proof. exact (EQ_MP (@lem5332518) (@lem0)). Qed.
Lemma lem5332520 : term694.
Proof. exact (@lem5332509 (@lem5332519)). Qed.
Lemma lem5332522 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332523 : term431 = term432.
Proof. exact (@lem5332522 (NUMERAL 0) term157). Qed.
Lemma lem5332524 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332525 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332526 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332525 h1) (fun h1 : term432 = True => @lem5332524)). Qed.
Lemma lem5332527 : term432 = True.
Proof. exact (EQ_MP (@lem5332526) (@lem5332524)). Qed.
Lemma lem5332528 : term431 = True.
Proof. exact (TRANS (@lem5332523) (@lem5332527)). Qed.
Lemma lem5332529 : True = term431.
Proof. exact (SYM (@lem5332528)). Qed.
Lemma lem5332530 : term431.
Proof. exact (EQ_MP (@lem5332529) (@lem0)). Qed.
Lemma lem5332531 : term695.
Proof. exact (@lem5332520 (@lem5332530)). Qed.
Lemma lem5332533 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332534 : term431 = term432.
Proof. exact (@lem5332533 (NUMERAL 0) term157). Qed.
Lemma lem5332535 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332536 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332537 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332536 h1) (fun h1 : term432 = True => @lem5332535)). Qed.
Lemma lem5332538 : term432 = True.
Proof. exact (EQ_MP (@lem5332537) (@lem5332535)). Qed.
Lemma lem5332539 : term431 = True.
Proof. exact (TRANS (@lem5332534) (@lem5332538)). Qed.
Lemma lem5332540 : True = term431.
Proof. exact (SYM (@lem5332539)). Qed.
Lemma lem5332541 : term431.
Proof. exact (EQ_MP (@lem5332540) (@lem0)). Qed.
Lemma lem5332542 : term696.
Proof. exact (@lem5332531 (@lem5332541)). Qed.
Lemma lem5332544 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332545 : term364 = term365.
Proof. exact (@lem5332544 term157 term157). Qed.
Lemma lem5332546 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332547 : term367 = term157.
Proof. exact (EQ_MP (@lem5332546) (@lem940073)). Qed.
Lemma lem5332548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332549 : term365 = term305.
Proof. exact (MK_COMB (@lem5332548) (@lem5332547)). Qed.
Lemma lem5332550 : term364 = term305.
Proof. exact (TRANS (@lem5332545) (@lem5332549)). Qed.
Lemma lem5332552 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5332553 : term398 = term403.
Proof. exact (@lem5332552 term157 term157). Qed.
Lemma lem5332554 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332555 : term367 = term157.
Proof. exact (EQ_MP (@lem5332554) (@lem940073)). Qed.
Lemma lem5332556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332557 : term365 = term305.
Proof. exact (MK_COMB (@lem5332556) (@lem5332555)). Qed.
Lemma lem5332558 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5332559 : term403 = term355.
Proof. exact (MK_COMB (@lem5332558) (@lem5332557)). Qed.
Lemma lem5332560 : term398 = term355.
Proof. exact (TRANS (@lem5332553) (@lem5332559)). Qed.
Lemma lem5332561 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332562 : term697 = term689.
Proof. exact (MK_COMB (@lem5332561) (@lem5332560)). Qed.
Lemma lem5332563 : term698 = term691.
Proof. exact (MK_COMB (@lem5332562) (@lem5332550)). Qed.
Lemma lem5332565 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5332566 : term691 = term293.
Proof. exact (@lem5332565 term157). Qed.
Lemma lem5332567 : term698 = term293.
Proof. exact (TRANS (@lem5332563) (@lem5332566)). Qed.
Lemma lem5332568 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332569 : term700 = term441.
Proof. exact (MK_COMB (@lem5332568) (@lem5332567)). Qed.
Lemma lem5332570 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5332571 : term701 = term443.
Proof. exact (MK_COMB (@lem5332569) (@lem5332570)). Qed.
Lemma lem5332573 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332574 : term443 = term293.
Proof. exact (@lem5332573 term157). Qed.
Lemma lem5332575 : term701 = term293.
Proof. exact (TRANS (@lem5332571) (@lem5332574)). Qed.
Lemma lem5332577 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332578 : term364 = term365.
Proof. exact (@lem5332577 term157 term157). Qed.
Lemma lem5332579 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332580 : term367 = term157.
Proof. exact (EQ_MP (@lem5332579) (@lem940073)). Qed.
Lemma lem5332581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332582 : term365 = term305.
Proof. exact (MK_COMB (@lem5332581) (@lem5332580)). Qed.
Lemma lem5332583 : term364 = term305.
Proof. exact (TRANS (@lem5332578) (@lem5332582)). Qed.
Lemma lem5332584 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5332585 : term445 = term443.
Proof. exact (MK_COMB (@lem5332584) (@lem5332583)). Qed.
Lemma lem5332587 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332588 : term443 = term293.
Proof. exact (@lem5332587 term157). Qed.
Lemma lem5332589 : term445 = term293.
Proof. exact (TRANS (@lem5332585) (@lem5332588)). Qed.
Lemma lem5332590 : term293 = term445.
Proof. exact (SYM (@lem5332589)). Qed.
Lemma lem5332591 : term701 = term445.
Proof. exact (TRANS (@lem5332575) (@lem5332590)). Qed.
Lemma lem5332592 : term692 = term352.
Proof. exact (@lem5332542 (@lem5332591)). Qed.
Lemma lem5332593 : term691 = term352.
Proof. exact (TRANS (@lem5332508) (@lem5332592)). Qed.
Lemma lem5332595 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5332596 : term352 = term293.
Proof. exact (@lem5332595 term293). Qed.
Lemma lem5332597 : term691 = term293.
Proof. exact (TRANS (@lem5332593) (@lem5332596)). Qed.
Lemma lem5332598 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332599 : term702 = term441.
Proof. exact (MK_COMB (@lem5332598) (@lem5332597)). Qed.
Lemma lem5332600 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5332601 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5332599) (@lem5332600 _69707)). Qed.
Lemma lem5332602 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5332499 _69707) (@lem5332601 _69707)). Qed.
Lemma lem5332603 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5332604 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5332602 _69707) (@lem5332603 _69707)). Qed.
Lemma lem5332605 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332606 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5332605) (@lem5332604 _69707)). Qed.
Lemma lem5332607 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5332608 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5332606 _69707) (@lem5332607)). Qed.
Lemma lem5332609 (_69707 : int) : (term706 _69707) = term710.
Proof. exact (TRANS (@lem5332498 _69707) (@lem5332608 _69707)). Qed.
Lemma lem5332610 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5332611 (_69707 : int) : (term706 _69707) = term355.
Proof. exact (TRANS (@lem5332609 _69707) (@lem5332610)). Qed.
Lemma lem5332612 (_69704 : int) (_69707 : int) : (term686 _69704 _69707) = term710.
Proof. exact (MK_COMB (@lem5332497 _69704) (@lem5332611 _69707)). Qed.
Lemma lem5332613 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term710.
Proof. exact (TRANS (@lem5332389 _69704 _69707) (@lem5332612 _69704 _69707)). Qed.
Lemma lem5332614 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5332615 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term355.
Proof. exact (TRANS (@lem5332613 _69704 _69707) (@lem5332614)). Qed.
Lemma lem5332616 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5332617 (_69704 : int) (_69707 : int) : (term711 _69704 _69707) = term712.
Proof. exact (MK_COMB (@lem5332616) (@lem5332615 _69704 _69707)). Qed.
Lemma lem5332618 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5332619 (_69704 : int) (_69707 : int) : (term684 _69704 _69707) = term713.
Proof. exact (MK_COMB (@lem5332617 _69704 _69707) (@lem5332618)). Qed.
Lemma lem5332620 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5332619 _69704 _69707) (@lem5332388 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332622 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5332623 : term713 = term714.
Proof. exact (@lem5332622 term293 term355). Qed.
Lemma lem5332625 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5332626 : term355 = term356.
Proof. exact (@lem5332625 term157). Qed.
Lemma lem5332628 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332629 : term293 = term352.
Proof. exact (@lem5332628 (NUMERAL 0)). Qed.
Lemma lem5332630 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5332631 : term295 = term715.
Proof. exact (MK_COMB (@lem5332630) (@lem5332629)). Qed.
Lemma lem5332632 : term714 = term716.
Proof. exact (MK_COMB (@lem5332631) (@lem5332626)). Qed.
Lemma lem5332633 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5332635 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332636 : term431 = term432.
Proof. exact (@lem5332635 (NUMERAL 0) term157). Qed.
Lemma lem5332637 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332638 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332639 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332638 h1) (fun h1 : term432 = True => @lem5332637)). Qed.
Lemma lem5332640 : term432 = True.
Proof. exact (EQ_MP (@lem5332639) (@lem5332637)). Qed.
Lemma lem5332641 : term431 = True.
Proof. exact (TRANS (@lem5332636) (@lem5332640)). Qed.
Lemma lem5332642 : True = term431.
Proof. exact (SYM (@lem5332641)). Qed.
Lemma lem5332643 : term431.
Proof. exact (EQ_MP (@lem5332642) (@lem0)). Qed.
Lemma lem5332644 : term718.
Proof. exact (@lem5332633 (@lem5332643)). Qed.
Lemma lem5332646 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332647 : term431 = term432.
Proof. exact (@lem5332646 (NUMERAL 0) term157). Qed.
Lemma lem5332648 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332649 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332650 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332649 h1) (fun h1 : term432 = True => @lem5332648)). Qed.
Lemma lem5332651 : term432 = True.
Proof. exact (EQ_MP (@lem5332650) (@lem5332648)). Qed.
Lemma lem5332652 : term431 = True.
Proof. exact (TRANS (@lem5332647) (@lem5332651)). Qed.
Lemma lem5332653 : True = term431.
Proof. exact (SYM (@lem5332652)). Qed.
Lemma lem5332654 : term431.
Proof. exact (EQ_MP (@lem5332653) (@lem0)). Qed.
Lemma lem5332655 : term716 = term719.
Proof. exact (@lem5332644 (@lem5332654)). Qed.
Lemma lem5332657 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5332658 : term398 = term403.
Proof. exact (@lem5332657 term157 term157). Qed.
Lemma lem5332659 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332660 : term367 = term157.
Proof. exact (EQ_MP (@lem5332659) (@lem940073)). Qed.
Lemma lem5332661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332662 : term365 = term305.
Proof. exact (MK_COMB (@lem5332661) (@lem5332660)). Qed.
Lemma lem5332663 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5332664 : term403 = term355.
Proof. exact (MK_COMB (@lem5332663) (@lem5332662)). Qed.
Lemma lem5332665 : term398 = term355.
Proof. exact (TRANS (@lem5332658) (@lem5332664)). Qed.
Lemma lem5332667 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332668 : term443 = term293.
Proof. exact (@lem5332667 term157). Qed.
Lemma lem5332669 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5332670 : term720 = term295.
Proof. exact (MK_COMB (@lem5332669) (@lem5332668)). Qed.
Lemma lem5332671 : term719 = term714.
Proof. exact (MK_COMB (@lem5332670) (@lem5332665)). Qed.
Lemma lem5332673 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5332674 : term714 = term723.
Proof. exact (@lem5332673 (NUMERAL 0) term157). Qed.
Lemma lem5332675 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332676 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5332677 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332676 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5332675)). Qed.
Lemma lem5332678 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5332677) (@lem5332675)). Qed.
Lemma lem5332679 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5332680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5332681 : term724 = (and True).
Proof. exact (MK_COMB (@lem5332680) (@lem5332679)). Qed.
Lemma lem5332682 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5332681) (@lem5332678)). Qed.
Lemma lem5332684 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5332685 : term723 = False.
Proof. exact (TRANS (@lem5332682) (@lem5332684)). Qed.
Lemma lem5332686 : term714 = False.
Proof. exact (TRANS (@lem5332674) (@lem5332685)). Qed.
Lemma lem5332687 : term719 = False.
Proof. exact (TRANS (@lem5332671) (@lem5332686)). Qed.
Lemma lem5332688 : term716 = False.
Proof. exact (TRANS (@lem5332655) (@lem5332687)). Qed.
Lemma lem5332689 : term714 = False.
Proof. exact (TRANS (@lem5332632) (@lem5332688)). Qed.
Lemma lem5332690 : term713 = False.
Proof. exact (TRANS (@lem5332623) (@lem5332689)). Qed.
Lemma lem5332691 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term661 _69706 _69704 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5332690) (@lem5332620 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332692 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term725 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5332693 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term654 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332692 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332695 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term623 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332693 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332697 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term592 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332695 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332699 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term561 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332697 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332701 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term530 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5332699 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332706 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term500 _69706 _69707.
Proof. exact (proj1 (@lem5332701 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332707 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term389 _69706 _69707.
Proof. exact (proj2 (@lem5332706 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332708 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term414 _69706 _69707.
Proof. exact (proj1 (@lem5332706 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332712 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5332713 : term662 = term431.
Proof. exact (@lem5332712 term293 term305). Qed.
Lemma lem5332715 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332716 : term305 = term397.
Proof. exact (@lem5332715 term157). Qed.
Lemma lem5332718 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332719 : term293 = term352.
Proof. exact (@lem5332718 (NUMERAL 0)). Qed.
Lemma lem5332720 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332721 : term663 = term664.
Proof. exact (MK_COMB (@lem5332720) (@lem5332719)). Qed.
Lemma lem5332722 : term431 = term665.
Proof. exact (MK_COMB (@lem5332721) (@lem5332716)). Qed.
Lemma lem5332723 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5332725 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332726 : term431 = term432.
Proof. exact (@lem5332725 (NUMERAL 0) term157). Qed.
Lemma lem5332727 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332728 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332729 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332728 h1) (fun h1 : term432 = True => @lem5332727)). Qed.
Lemma lem5332730 : term432 = True.
Proof. exact (EQ_MP (@lem5332729) (@lem5332727)). Qed.
Lemma lem5332731 : term431 = True.
Proof. exact (TRANS (@lem5332726) (@lem5332730)). Qed.
Lemma lem5332732 : True = term431.
Proof. exact (SYM (@lem5332731)). Qed.
Lemma lem5332733 : term431.
Proof. exact (EQ_MP (@lem5332732) (@lem0)). Qed.
Lemma lem5332734 : term667.
Proof. exact (@lem5332723 (@lem5332733)). Qed.
Lemma lem5332736 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332737 : term431 = term432.
Proof. exact (@lem5332736 (NUMERAL 0) term157). Qed.
Lemma lem5332738 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332739 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332740 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332739 h1) (fun h1 : term432 = True => @lem5332738)). Qed.
Lemma lem5332741 : term432 = True.
Proof. exact (EQ_MP (@lem5332740) (@lem5332738)). Qed.
Lemma lem5332742 : term431 = True.
Proof. exact (TRANS (@lem5332737) (@lem5332741)). Qed.
Lemma lem5332743 : True = term431.
Proof. exact (SYM (@lem5332742)). Qed.
Lemma lem5332744 : term431.
Proof. exact (EQ_MP (@lem5332743) (@lem0)). Qed.
Lemma lem5332745 : term665 = term668.
Proof. exact (@lem5332734 (@lem5332744)). Qed.
Lemma lem5332747 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332748 : term364 = term365.
Proof. exact (@lem5332747 term157 term157). Qed.
Lemma lem5332749 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332750 : term367 = term157.
Proof. exact (EQ_MP (@lem5332749) (@lem940073)). Qed.
Lemma lem5332751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332752 : term365 = term305.
Proof. exact (MK_COMB (@lem5332751) (@lem5332750)). Qed.
Lemma lem5332753 : term364 = term305.
Proof. exact (TRANS (@lem5332748) (@lem5332752)). Qed.
Lemma lem5332755 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332756 : term443 = term293.
Proof. exact (@lem5332755 term157). Qed.
Lemma lem5332757 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332758 : term669 = term663.
Proof. exact (MK_COMB (@lem5332757) (@lem5332756)). Qed.
Lemma lem5332759 : term668 = term431.
Proof. exact (MK_COMB (@lem5332758) (@lem5332753)). Qed.
Lemma lem5332761 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332762 : term431 = term432.
Proof. exact (@lem5332761 (NUMERAL 0) term157). Qed.
Lemma lem5332763 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332764 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332765 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332764 h1) (fun h1 : term432 = True => @lem5332763)). Qed.
Lemma lem5332766 : term432 = True.
Proof. exact (EQ_MP (@lem5332765) (@lem5332763)). Qed.
Lemma lem5332767 : term431 = True.
Proof. exact (TRANS (@lem5332762) (@lem5332766)). Qed.
Lemma lem5332768 : term668 = True.
Proof. exact (TRANS (@lem5332759) (@lem5332767)). Qed.
Lemma lem5332769 : term665 = True.
Proof. exact (TRANS (@lem5332745) (@lem5332768)). Qed.
Lemma lem5332770 : term431 = True.
Proof. exact (TRANS (@lem5332722) (@lem5332769)). Qed.
Lemma lem5332771 : term662 = True.
Proof. exact (TRANS (@lem5332713) (@lem5332770)). Qed.
Lemma lem5332772 : True = term662.
Proof. exact (SYM (@lem5332771)). Qed.
Lemma lem5332773 : term662.
Proof. exact (EQ_MP (@lem5332772) (@lem0)). Qed.
Lemma lem5332774 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term726 _69706 _69707.
Proof. exact (conj (@lem5332773) (@lem5332707 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332776 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5332777 (_69706 : int) (_69707 : int) : term727 _69706 _69707.
Proof. exact (@lem5332776 term305 (term386 _69706 _69707)). Qed.
Lemma lem5332778 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term728 _69706 _69707.
Proof. exact (@lem5332777 _69706 _69707 (@lem5332774 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332779 (_69706 : int) (_69707 : int) : (term729 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (@lem1982733 (term386 _69706 _69707)). Qed.
Lemma lem5332780 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5332781 (_69706 : int) (_69707 : int) : (term730 _69706 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5332780) (@lem5332779 _69706 _69707)). Qed.
Lemma lem5332782 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5332783 (_69706 : int) (_69707 : int) : (term728 _69706 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5332781 _69706 _69707) (@lem5332782)). Qed.
Lemma lem5332784 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term389 _69706 _69707.
Proof. exact (EQ_MP (@lem5332783 _69706 _69707) (@lem5332778 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332786 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5332787 : term662 = term431.
Proof. exact (@lem5332786 term293 term305). Qed.
Lemma lem5332789 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332790 : term305 = term397.
Proof. exact (@lem5332789 term157). Qed.
Lemma lem5332792 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332793 : term293 = term352.
Proof. exact (@lem5332792 (NUMERAL 0)). Qed.
Lemma lem5332794 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332795 : term663 = term664.
Proof. exact (MK_COMB (@lem5332794) (@lem5332793)). Qed.
Lemma lem5332796 : term431 = term665.
Proof. exact (MK_COMB (@lem5332795) (@lem5332790)). Qed.
Lemma lem5332797 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5332799 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332800 : term431 = term432.
Proof. exact (@lem5332799 (NUMERAL 0) term157). Qed.
Lemma lem5332801 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332802 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332803 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332802 h1) (fun h1 : term432 = True => @lem5332801)). Qed.
Lemma lem5332804 : term432 = True.
Proof. exact (EQ_MP (@lem5332803) (@lem5332801)). Qed.
Lemma lem5332805 : term431 = True.
Proof. exact (TRANS (@lem5332800) (@lem5332804)). Qed.
Lemma lem5332806 : True = term431.
Proof. exact (SYM (@lem5332805)). Qed.
Lemma lem5332807 : term431.
Proof. exact (EQ_MP (@lem5332806) (@lem0)). Qed.
Lemma lem5332808 : term667.
Proof. exact (@lem5332797 (@lem5332807)). Qed.
Lemma lem5332810 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332811 : term431 = term432.
Proof. exact (@lem5332810 (NUMERAL 0) term157). Qed.
Lemma lem5332812 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332813 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332814 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332813 h1) (fun h1 : term432 = True => @lem5332812)). Qed.
Lemma lem5332815 : term432 = True.
Proof. exact (EQ_MP (@lem5332814) (@lem5332812)). Qed.
Lemma lem5332816 : term431 = True.
Proof. exact (TRANS (@lem5332811) (@lem5332815)). Qed.
Lemma lem5332817 : True = term431.
Proof. exact (SYM (@lem5332816)). Qed.
Lemma lem5332818 : term431.
Proof. exact (EQ_MP (@lem5332817) (@lem0)). Qed.
Lemma lem5332819 : term665 = term668.
Proof. exact (@lem5332808 (@lem5332818)). Qed.
Lemma lem5332821 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332822 : term364 = term365.
Proof. exact (@lem5332821 term157 term157). Qed.
Lemma lem5332823 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332824 : term367 = term157.
Proof. exact (EQ_MP (@lem5332823) (@lem940073)). Qed.
Lemma lem5332825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332826 : term365 = term305.
Proof. exact (MK_COMB (@lem5332825) (@lem5332824)). Qed.
Lemma lem5332827 : term364 = term305.
Proof. exact (TRANS (@lem5332822) (@lem5332826)). Qed.
Lemma lem5332829 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332830 : term443 = term293.
Proof. exact (@lem5332829 term157). Qed.
Lemma lem5332831 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5332832 : term669 = term663.
Proof. exact (MK_COMB (@lem5332831) (@lem5332830)). Qed.
Lemma lem5332833 : term668 = term431.
Proof. exact (MK_COMB (@lem5332832) (@lem5332827)). Qed.
Lemma lem5332835 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332836 : term431 = term432.
Proof. exact (@lem5332835 (NUMERAL 0) term157). Qed.
Lemma lem5332837 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332838 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332839 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332838 h1) (fun h1 : term432 = True => @lem5332837)). Qed.
Lemma lem5332840 : term432 = True.
Proof. exact (EQ_MP (@lem5332839) (@lem5332837)). Qed.
Lemma lem5332841 : term431 = True.
Proof. exact (TRANS (@lem5332836) (@lem5332840)). Qed.
Lemma lem5332842 : term668 = True.
Proof. exact (TRANS (@lem5332833) (@lem5332841)). Qed.
Lemma lem5332843 : term665 = True.
Proof. exact (TRANS (@lem5332819) (@lem5332842)). Qed.
Lemma lem5332844 : term431 = True.
Proof. exact (TRANS (@lem5332796) (@lem5332843)). Qed.
Lemma lem5332845 : term662 = True.
Proof. exact (TRANS (@lem5332787) (@lem5332844)). Qed.
Lemma lem5332846 : True = term662.
Proof. exact (SYM (@lem5332845)). Qed.
Lemma lem5332847 : term662.
Proof. exact (EQ_MP (@lem5332846) (@lem0)). Qed.
Lemma lem5332848 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term731 _69706 _69707.
Proof. exact (conj (@lem5332847) (@lem5332708 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332850 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5332851 (_69706 : int) (_69707 : int) : term732 _69706 _69707.
Proof. exact (@lem5332850 term305 (term412 _69706 _69707)). Qed.
Lemma lem5332852 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term733 _69706 _69707.
Proof. exact (@lem5332851 _69706 _69707 (@lem5332848 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332853 (_69706 : int) (_69707 : int) : (term734 _69706 _69707) = (term412 _69706 _69707).
Proof. exact (@lem1982733 (term412 _69706 _69707)). Qed.
Lemma lem5332854 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5332855 (_69706 : int) (_69707 : int) : (term735 _69706 _69707) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5332854) (@lem5332853 _69706 _69707)). Qed.
Lemma lem5332856 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5332857 (_69706 : int) (_69707 : int) : (term733 _69706 _69707) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5332855 _69706 _69707) (@lem5332856)). Qed.
Lemma lem5332858 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term414 _69706 _69707.
Proof. exact (EQ_MP (@lem5332857 _69706 _69707) (@lem5332852 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332859 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term500 _69706 _69707.
Proof. exact (conj (@lem5332858 _69706 _69704 _69705 _69707 h1) (@lem5332784 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332861 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5332862 (_69706 : int) (_69707 : int) : term736 _69706 _69707.
Proof. exact (@lem5332861 (term412 _69706 _69707) (term386 _69706 _69707)). Qed.
Lemma lem5332863 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term737 _69706 _69707.
Proof. exact (@lem5332862 _69706 _69707 (@lem5332859 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5332864 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = (term739 _69706 _69707).
Proof. exact (@lem1982753 (term380 _69706) (real_of_int _69706) (term740 _69707) (term380 _69707)). Qed.
Lemma lem5332865 (_69706 : int) : (term687 _69706) = (term688 _69706).
Proof. exact (@lem1982713 term355 (real_of_int _69706)). Qed.
Lemma lem5332867 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332868 : term305 = term397.
Proof. exact (@lem5332867 term157). Qed.
Lemma lem5332870 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5332871 : term355 = term356.
Proof. exact (@lem5332870 term157). Qed.
Lemma lem5332872 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332873 : term689 = term690.
Proof. exact (MK_COMB (@lem5332872) (@lem5332871)). Qed.
Lemma lem5332874 : term691 = term692.
Proof. exact (MK_COMB (@lem5332873) (@lem5332868)). Qed.
Lemma lem5332875 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5332877 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332878 : term431 = term432.
Proof. exact (@lem5332877 (NUMERAL 0) term157). Qed.
Lemma lem5332879 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332880 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332881 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332880 h1) (fun h1 : term432 = True => @lem5332879)). Qed.
Lemma lem5332882 : term432 = True.
Proof. exact (EQ_MP (@lem5332881) (@lem5332879)). Qed.
Lemma lem5332883 : term431 = True.
Proof. exact (TRANS (@lem5332878) (@lem5332882)). Qed.
Lemma lem5332884 : True = term431.
Proof. exact (SYM (@lem5332883)). Qed.
Lemma lem5332885 : term431.
Proof. exact (EQ_MP (@lem5332884) (@lem0)). Qed.
Lemma lem5332886 : term694.
Proof. exact (@lem5332875 (@lem5332885)). Qed.
Lemma lem5332888 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332889 : term431 = term432.
Proof. exact (@lem5332888 (NUMERAL 0) term157). Qed.
Lemma lem5332890 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332891 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332892 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332891 h1) (fun h1 : term432 = True => @lem5332890)). Qed.
Lemma lem5332893 : term432 = True.
Proof. exact (EQ_MP (@lem5332892) (@lem5332890)). Qed.
Lemma lem5332894 : term431 = True.
Proof. exact (TRANS (@lem5332889) (@lem5332893)). Qed.
Lemma lem5332895 : True = term431.
Proof. exact (SYM (@lem5332894)). Qed.
Lemma lem5332896 : term431.
Proof. exact (EQ_MP (@lem5332895) (@lem0)). Qed.
Lemma lem5332897 : term695.
Proof. exact (@lem5332886 (@lem5332896)). Qed.
Lemma lem5332899 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332900 : term431 = term432.
Proof. exact (@lem5332899 (NUMERAL 0) term157). Qed.
Lemma lem5332901 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332902 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332903 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332902 h1) (fun h1 : term432 = True => @lem5332901)). Qed.
Lemma lem5332904 : term432 = True.
Proof. exact (EQ_MP (@lem5332903) (@lem5332901)). Qed.
Lemma lem5332905 : term431 = True.
Proof. exact (TRANS (@lem5332900) (@lem5332904)). Qed.
Lemma lem5332906 : True = term431.
Proof. exact (SYM (@lem5332905)). Qed.
Lemma lem5332907 : term431.
Proof. exact (EQ_MP (@lem5332906) (@lem0)). Qed.
Lemma lem5332908 : term696.
Proof. exact (@lem5332897 (@lem5332907)). Qed.
Lemma lem5332910 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332911 : term364 = term365.
Proof. exact (@lem5332910 term157 term157). Qed.
Lemma lem5332912 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332913 : term367 = term157.
Proof. exact (EQ_MP (@lem5332912) (@lem940073)). Qed.
Lemma lem5332914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332915 : term365 = term305.
Proof. exact (MK_COMB (@lem5332914) (@lem5332913)). Qed.
Lemma lem5332916 : term364 = term305.
Proof. exact (TRANS (@lem5332911) (@lem5332915)). Qed.
Lemma lem5332918 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5332919 : term398 = term403.
Proof. exact (@lem5332918 term157 term157). Qed.
Lemma lem5332920 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332921 : term367 = term157.
Proof. exact (EQ_MP (@lem5332920) (@lem940073)). Qed.
Lemma lem5332922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332923 : term365 = term305.
Proof. exact (MK_COMB (@lem5332922) (@lem5332921)). Qed.
Lemma lem5332924 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5332925 : term403 = term355.
Proof. exact (MK_COMB (@lem5332924) (@lem5332923)). Qed.
Lemma lem5332926 : term398 = term355.
Proof. exact (TRANS (@lem5332919) (@lem5332925)). Qed.
Lemma lem5332927 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332928 : term697 = term689.
Proof. exact (MK_COMB (@lem5332927) (@lem5332926)). Qed.
Lemma lem5332929 : term698 = term691.
Proof. exact (MK_COMB (@lem5332928) (@lem5332916)). Qed.
Lemma lem5332931 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5332932 : term691 = term293.
Proof. exact (@lem5332931 term157). Qed.
Lemma lem5332933 : term698 = term293.
Proof. exact (TRANS (@lem5332929) (@lem5332932)). Qed.
Lemma lem5332934 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332935 : term700 = term441.
Proof. exact (MK_COMB (@lem5332934) (@lem5332933)). Qed.
Lemma lem5332936 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5332937 : term701 = term443.
Proof. exact (MK_COMB (@lem5332935) (@lem5332936)). Qed.
Lemma lem5332939 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332940 : term443 = term293.
Proof. exact (@lem5332939 term157). Qed.
Lemma lem5332941 : term701 = term293.
Proof. exact (TRANS (@lem5332937) (@lem5332940)). Qed.
Lemma lem5332943 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5332944 : term364 = term365.
Proof. exact (@lem5332943 term157 term157). Qed.
Lemma lem5332945 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5332946 : term367 = term157.
Proof. exact (EQ_MP (@lem5332945) (@lem940073)). Qed.
Lemma lem5332947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5332948 : term365 = term305.
Proof. exact (MK_COMB (@lem5332947) (@lem5332946)). Qed.
Lemma lem5332949 : term364 = term305.
Proof. exact (TRANS (@lem5332944) (@lem5332948)). Qed.
Lemma lem5332950 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5332951 : term445 = term443.
Proof. exact (MK_COMB (@lem5332950) (@lem5332949)). Qed.
Lemma lem5332953 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5332954 : term443 = term293.
Proof. exact (@lem5332953 term157). Qed.
Lemma lem5332955 : term445 = term293.
Proof. exact (TRANS (@lem5332951) (@lem5332954)). Qed.
Lemma lem5332956 : term293 = term445.
Proof. exact (SYM (@lem5332955)). Qed.
Lemma lem5332957 : term701 = term445.
Proof. exact (TRANS (@lem5332941) (@lem5332956)). Qed.
Lemma lem5332958 : term692 = term352.
Proof. exact (@lem5332908 (@lem5332957)). Qed.
Lemma lem5332959 : term691 = term352.
Proof. exact (TRANS (@lem5332874) (@lem5332958)). Qed.
Lemma lem5332961 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5332962 : term352 = term293.
Proof. exact (@lem5332961 term293). Qed.
Lemma lem5332963 : term691 = term293.
Proof. exact (TRANS (@lem5332959) (@lem5332962)). Qed.
Lemma lem5332964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5332965 : term702 = term441.
Proof. exact (MK_COMB (@lem5332964) (@lem5332963)). Qed.
Lemma lem5332966 (_69706 : int) : (real_of_int _69706) = (real_of_int _69706).
Proof. exact (eq_refl (real_of_int _69706)). Qed.
Lemma lem5332967 (_69706 : int) : (term688 _69706) = (term703 _69706).
Proof. exact (MK_COMB (@lem5332965) (@lem5332966 _69706)). Qed.
Lemma lem5332968 (_69706 : int) : (term687 _69706) = (term703 _69706).
Proof. exact (TRANS (@lem5332865 _69706) (@lem5332967 _69706)). Qed.
Lemma lem5332969 (_69706 : int) : (term703 _69706) = term293.
Proof. exact (@lem1982719 (real_of_int _69706)). Qed.
Lemma lem5332970 (_69706 : int) : (term687 _69706) = term293.
Proof. exact (TRANS (@lem5332968 _69706) (@lem5332969 _69706)). Qed.
Lemma lem5332971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332972 (_69706 : int) : (term704 _69706) = term705.
Proof. exact (MK_COMB (@lem5332971) (@lem5332970 _69706)). Qed.
Lemma lem5332973 (_69707 : int) : (term741 _69707) = (term707 _69707).
Proof. exact (@lem1982759 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5332974 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5332976 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5332977 : term305 = term397.
Proof. exact (@lem5332976 term157). Qed.
Lemma lem5332979 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5332980 : term355 = term356.
Proof. exact (@lem5332979 term157). Qed.
Lemma lem5332981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5332982 : term689 = term690.
Proof. exact (MK_COMB (@lem5332981) (@lem5332980)). Qed.
Lemma lem5332983 : term691 = term692.
Proof. exact (MK_COMB (@lem5332982) (@lem5332977)). Qed.
Lemma lem5332984 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5332986 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332987 : term431 = term432.
Proof. exact (@lem5332986 (NUMERAL 0) term157). Qed.
Lemma lem5332988 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5332989 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5332990 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5332989 h1) (fun h1 : term432 = True => @lem5332988)). Qed.
Lemma lem5332991 : term432 = True.
Proof. exact (EQ_MP (@lem5332990) (@lem5332988)). Qed.
Lemma lem5332992 : term431 = True.
Proof. exact (TRANS (@lem5332987) (@lem5332991)). Qed.
Lemma lem5332993 : True = term431.
Proof. exact (SYM (@lem5332992)). Qed.
Lemma lem5332994 : term431.
Proof. exact (EQ_MP (@lem5332993) (@lem0)). Qed.
Lemma lem5332995 : term694.
Proof. exact (@lem5332984 (@lem5332994)). Qed.
Lemma lem5332997 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5332998 : term431 = term432.
Proof. exact (@lem5332997 (NUMERAL 0) term157). Qed.
Lemma lem5332999 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333000 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333001 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333000 h1) (fun h1 : term432 = True => @lem5332999)). Qed.
Lemma lem5333002 : term432 = True.
Proof. exact (EQ_MP (@lem5333001) (@lem5332999)). Qed.
Lemma lem5333003 : term431 = True.
Proof. exact (TRANS (@lem5332998) (@lem5333002)). Qed.
Lemma lem5333004 : True = term431.
Proof. exact (SYM (@lem5333003)). Qed.
Lemma lem5333005 : term431.
Proof. exact (EQ_MP (@lem5333004) (@lem0)). Qed.
Lemma lem5333006 : term695.
Proof. exact (@lem5332995 (@lem5333005)). Qed.
Lemma lem5333008 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333009 : term431 = term432.
Proof. exact (@lem5333008 (NUMERAL 0) term157). Qed.
Lemma lem5333010 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333011 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333012 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333011 h1) (fun h1 : term432 = True => @lem5333010)). Qed.
Lemma lem5333013 : term432 = True.
Proof. exact (EQ_MP (@lem5333012) (@lem5333010)). Qed.
Lemma lem5333014 : term431 = True.
Proof. exact (TRANS (@lem5333009) (@lem5333013)). Qed.
Lemma lem5333015 : True = term431.
Proof. exact (SYM (@lem5333014)). Qed.
Lemma lem5333016 : term431.
Proof. exact (EQ_MP (@lem5333015) (@lem0)). Qed.
Lemma lem5333017 : term696.
Proof. exact (@lem5333006 (@lem5333016)). Qed.
Lemma lem5333019 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333020 : term364 = term365.
Proof. exact (@lem5333019 term157 term157). Qed.
Lemma lem5333021 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333022 : term367 = term157.
Proof. exact (EQ_MP (@lem5333021) (@lem940073)). Qed.
Lemma lem5333023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333024 : term365 = term305.
Proof. exact (MK_COMB (@lem5333023) (@lem5333022)). Qed.
Lemma lem5333025 : term364 = term305.
Proof. exact (TRANS (@lem5333020) (@lem5333024)). Qed.
Lemma lem5333027 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333028 : term398 = term403.
Proof. exact (@lem5333027 term157 term157). Qed.
Lemma lem5333029 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333030 : term367 = term157.
Proof. exact (EQ_MP (@lem5333029) (@lem940073)). Qed.
Lemma lem5333031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333032 : term365 = term305.
Proof. exact (MK_COMB (@lem5333031) (@lem5333030)). Qed.
Lemma lem5333033 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333034 : term403 = term355.
Proof. exact (MK_COMB (@lem5333033) (@lem5333032)). Qed.
Lemma lem5333035 : term398 = term355.
Proof. exact (TRANS (@lem5333028) (@lem5333034)). Qed.
Lemma lem5333036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333037 : term697 = term689.
Proof. exact (MK_COMB (@lem5333036) (@lem5333035)). Qed.
Lemma lem5333038 : term698 = term691.
Proof. exact (MK_COMB (@lem5333037) (@lem5333025)). Qed.
Lemma lem5333040 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5333041 : term691 = term293.
Proof. exact (@lem5333040 term157). Qed.
Lemma lem5333042 : term698 = term293.
Proof. exact (TRANS (@lem5333038) (@lem5333041)). Qed.
Lemma lem5333043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333044 : term700 = term441.
Proof. exact (MK_COMB (@lem5333043) (@lem5333042)). Qed.
Lemma lem5333045 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5333046 : term701 = term443.
Proof. exact (MK_COMB (@lem5333044) (@lem5333045)). Qed.
Lemma lem5333048 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333049 : term443 = term293.
Proof. exact (@lem5333048 term157). Qed.
Lemma lem5333050 : term701 = term293.
Proof. exact (TRANS (@lem5333046) (@lem5333049)). Qed.
Lemma lem5333052 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333053 : term364 = term365.
Proof. exact (@lem5333052 term157 term157). Qed.
Lemma lem5333054 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333055 : term367 = term157.
Proof. exact (EQ_MP (@lem5333054) (@lem940073)). Qed.
Lemma lem5333056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333057 : term365 = term305.
Proof. exact (MK_COMB (@lem5333056) (@lem5333055)). Qed.
Lemma lem5333058 : term364 = term305.
Proof. exact (TRANS (@lem5333053) (@lem5333057)). Qed.
Lemma lem5333059 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5333060 : term445 = term443.
Proof. exact (MK_COMB (@lem5333059) (@lem5333058)). Qed.
Lemma lem5333062 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333063 : term443 = term293.
Proof. exact (@lem5333062 term157). Qed.
Lemma lem5333064 : term445 = term293.
Proof. exact (TRANS (@lem5333060) (@lem5333063)). Qed.
Lemma lem5333065 : term293 = term445.
Proof. exact (SYM (@lem5333064)). Qed.
Lemma lem5333066 : term701 = term445.
Proof. exact (TRANS (@lem5333050) (@lem5333065)). Qed.
Lemma lem5333067 : term692 = term352.
Proof. exact (@lem5333017 (@lem5333066)). Qed.
Lemma lem5333068 : term691 = term352.
Proof. exact (TRANS (@lem5332983) (@lem5333067)). Qed.
Lemma lem5333070 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5333071 : term352 = term293.
Proof. exact (@lem5333070 term293). Qed.
Lemma lem5333072 : term691 = term293.
Proof. exact (TRANS (@lem5333068) (@lem5333071)). Qed.
Lemma lem5333073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333074 : term702 = term441.
Proof. exact (MK_COMB (@lem5333073) (@lem5333072)). Qed.
Lemma lem5333075 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5333076 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5333074) (@lem5333075 _69707)). Qed.
Lemma lem5333077 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5332974 _69707) (@lem5333076 _69707)). Qed.
Lemma lem5333078 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5333079 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5333077 _69707) (@lem5333078 _69707)). Qed.
Lemma lem5333080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333081 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5333080) (@lem5333079 _69707)). Qed.
Lemma lem5333082 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5333083 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5333081 _69707) (@lem5333082)). Qed.
Lemma lem5333084 (_69707 : int) : (term741 _69707) = term710.
Proof. exact (TRANS (@lem5332973 _69707) (@lem5333083 _69707)). Qed.
Lemma lem5333085 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5333086 (_69707 : int) : (term741 _69707) = term355.
Proof. exact (TRANS (@lem5333084 _69707) (@lem5333085)). Qed.
Lemma lem5333087 (_69706 : int) (_69707 : int) : (term739 _69706 _69707) = term710.
Proof. exact (MK_COMB (@lem5332972 _69706) (@lem5333086 _69707)). Qed.
Lemma lem5333088 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = term710.
Proof. exact (TRANS (@lem5332864 _69706 _69707) (@lem5333087 _69706 _69707)). Qed.
Lemma lem5333089 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5333090 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = term355.
Proof. exact (TRANS (@lem5333088 _69706 _69707) (@lem5333089)). Qed.
Lemma lem5333091 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333092 (_69706 : int) (_69707 : int) : (term742 _69706 _69707) = term712.
Proof. exact (MK_COMB (@lem5333091) (@lem5333090 _69706 _69707)). Qed.
Lemma lem5333093 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333094 (_69706 : int) (_69707 : int) : (term737 _69706 _69707) = term713.
Proof. exact (MK_COMB (@lem5333092 _69706 _69707) (@lem5333093)). Qed.
Lemma lem5333095 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5333094 _69706 _69707) (@lem5332863 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333097 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5333098 : term713 = term714.
Proof. exact (@lem5333097 term293 term355). Qed.
Lemma lem5333100 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333101 : term355 = term356.
Proof. exact (@lem5333100 term157). Qed.
Lemma lem5333103 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333104 : term293 = term352.
Proof. exact (@lem5333103 (NUMERAL 0)). Qed.
Lemma lem5333105 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5333106 : term295 = term715.
Proof. exact (MK_COMB (@lem5333105) (@lem5333104)). Qed.
Lemma lem5333107 : term714 = term716.
Proof. exact (MK_COMB (@lem5333106) (@lem5333101)). Qed.
Lemma lem5333108 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5333110 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333111 : term431 = term432.
Proof. exact (@lem5333110 (NUMERAL 0) term157). Qed.
Lemma lem5333112 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333113 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333114 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333113 h1) (fun h1 : term432 = True => @lem5333112)). Qed.
Lemma lem5333115 : term432 = True.
Proof. exact (EQ_MP (@lem5333114) (@lem5333112)). Qed.
Lemma lem5333116 : term431 = True.
Proof. exact (TRANS (@lem5333111) (@lem5333115)). Qed.
Lemma lem5333117 : True = term431.
Proof. exact (SYM (@lem5333116)). Qed.
Lemma lem5333118 : term431.
Proof. exact (EQ_MP (@lem5333117) (@lem0)). Qed.
Lemma lem5333119 : term718.
Proof. exact (@lem5333108 (@lem5333118)). Qed.
Lemma lem5333121 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333122 : term431 = term432.
Proof. exact (@lem5333121 (NUMERAL 0) term157). Qed.
Lemma lem5333123 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333124 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333125 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333124 h1) (fun h1 : term432 = True => @lem5333123)). Qed.
Lemma lem5333126 : term432 = True.
Proof. exact (EQ_MP (@lem5333125) (@lem5333123)). Qed.
Lemma lem5333127 : term431 = True.
Proof. exact (TRANS (@lem5333122) (@lem5333126)). Qed.
Lemma lem5333128 : True = term431.
Proof. exact (SYM (@lem5333127)). Qed.
Lemma lem5333129 : term431.
Proof. exact (EQ_MP (@lem5333128) (@lem0)). Qed.
Lemma lem5333130 : term716 = term719.
Proof. exact (@lem5333119 (@lem5333129)). Qed.
Lemma lem5333132 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333133 : term398 = term403.
Proof. exact (@lem5333132 term157 term157). Qed.
Lemma lem5333134 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333135 : term367 = term157.
Proof. exact (EQ_MP (@lem5333134) (@lem940073)). Qed.
Lemma lem5333136 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333137 : term365 = term305.
Proof. exact (MK_COMB (@lem5333136) (@lem5333135)). Qed.
Lemma lem5333138 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333139 : term403 = term355.
Proof. exact (MK_COMB (@lem5333138) (@lem5333137)). Qed.
Lemma lem5333140 : term398 = term355.
Proof. exact (TRANS (@lem5333133) (@lem5333139)). Qed.
Lemma lem5333142 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333143 : term443 = term293.
Proof. exact (@lem5333142 term157). Qed.
Lemma lem5333144 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5333145 : term720 = term295.
Proof. exact (MK_COMB (@lem5333144) (@lem5333143)). Qed.
Lemma lem5333146 : term719 = term714.
Proof. exact (MK_COMB (@lem5333145) (@lem5333140)). Qed.
Lemma lem5333148 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5333149 : term714 = term723.
Proof. exact (@lem5333148 (NUMERAL 0) term157). Qed.
Lemma lem5333150 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333151 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5333152 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333151 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5333150)). Qed.
Lemma lem5333153 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5333152) (@lem5333150)). Qed.
Lemma lem5333154 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5333155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5333156 : term724 = (and True).
Proof. exact (MK_COMB (@lem5333155) (@lem5333154)). Qed.
Lemma lem5333157 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5333156) (@lem5333153)). Qed.
Lemma lem5333159 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5333160 : term723 = False.
Proof. exact (TRANS (@lem5333157) (@lem5333159)). Qed.
Lemma lem5333161 : term714 = False.
Proof. exact (TRANS (@lem5333149) (@lem5333160)). Qed.
Lemma lem5333162 : term719 = False.
Proof. exact (TRANS (@lem5333146) (@lem5333161)). Qed.
Lemma lem5333163 : term716 = False.
Proof. exact (TRANS (@lem5333130) (@lem5333162)). Qed.
Lemma lem5333164 : term714 = False.
Proof. exact (TRANS (@lem5333107) (@lem5333163)). Qed.
Lemma lem5333165 : term713 = False.
Proof. exact (TRANS (@lem5333098) (@lem5333164)). Qed.
Lemma lem5333166 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term725 _69706 _69704 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5333165) (@lem5333095 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333167 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term652 _69706 _69704 _69705 _69707) : False.
Proof. exact (or_elim (@lem5332216 _69706 _69704 _69705 _69707 h1) (fun h0 : term661 _69706 _69704 _69705 _69707 => @lem5332691 _69706 _69704 _69705 _69707 h0) (fun h0 : term725 _69706 _69704 _69705 _69707 => @lem5333166 _69706 _69704 _69705 _69707 h0)). Qed.
Lemma lem5333168 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term648 _69706 _69704 _69705 _69707) : term648 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5333169 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term743 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5333170 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term649 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333169 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333172 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term618 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333170 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333174 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term587 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333172 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333176 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term556 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333174 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333178 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term525 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333176 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333182 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term456 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333178 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333183 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term495 _69704 _69705 _69707.
Proof. exact (proj1 (@lem5333178 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333185 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term411 _69704 _69707.
Proof. exact (proj1 (@lem5333183 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333187 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term454 _69704 _69707.
Proof. exact (proj1 (@lem5333182 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333189 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5333190 : term662 = term431.
Proof. exact (@lem5333189 term293 term305). Qed.
Lemma lem5333192 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333193 : term305 = term397.
Proof. exact (@lem5333192 term157). Qed.
Lemma lem5333195 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333196 : term293 = term352.
Proof. exact (@lem5333195 (NUMERAL 0)). Qed.
Lemma lem5333197 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333198 : term663 = term664.
Proof. exact (MK_COMB (@lem5333197) (@lem5333196)). Qed.
Lemma lem5333199 : term431 = term665.
Proof. exact (MK_COMB (@lem5333198) (@lem5333193)). Qed.
Lemma lem5333200 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5333202 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333203 : term431 = term432.
Proof. exact (@lem5333202 (NUMERAL 0) term157). Qed.
Lemma lem5333204 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333205 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333206 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333205 h1) (fun h1 : term432 = True => @lem5333204)). Qed.
Lemma lem5333207 : term432 = True.
Proof. exact (EQ_MP (@lem5333206) (@lem5333204)). Qed.
Lemma lem5333208 : term431 = True.
Proof. exact (TRANS (@lem5333203) (@lem5333207)). Qed.
Lemma lem5333209 : True = term431.
Proof. exact (SYM (@lem5333208)). Qed.
Lemma lem5333210 : term431.
Proof. exact (EQ_MP (@lem5333209) (@lem0)). Qed.
Lemma lem5333211 : term667.
Proof. exact (@lem5333200 (@lem5333210)). Qed.
Lemma lem5333213 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333214 : term431 = term432.
Proof. exact (@lem5333213 (NUMERAL 0) term157). Qed.
Lemma lem5333215 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333216 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333217 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333216 h1) (fun h1 : term432 = True => @lem5333215)). Qed.
Lemma lem5333218 : term432 = True.
Proof. exact (EQ_MP (@lem5333217) (@lem5333215)). Qed.
Lemma lem5333219 : term431 = True.
Proof. exact (TRANS (@lem5333214) (@lem5333218)). Qed.
Lemma lem5333220 : True = term431.
Proof. exact (SYM (@lem5333219)). Qed.
Lemma lem5333221 : term431.
Proof. exact (EQ_MP (@lem5333220) (@lem0)). Qed.
Lemma lem5333222 : term665 = term668.
Proof. exact (@lem5333211 (@lem5333221)). Qed.
Lemma lem5333224 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333225 : term364 = term365.
Proof. exact (@lem5333224 term157 term157). Qed.
Lemma lem5333226 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333227 : term367 = term157.
Proof. exact (EQ_MP (@lem5333226) (@lem940073)). Qed.
Lemma lem5333228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333229 : term365 = term305.
Proof. exact (MK_COMB (@lem5333228) (@lem5333227)). Qed.
Lemma lem5333230 : term364 = term305.
Proof. exact (TRANS (@lem5333225) (@lem5333229)). Qed.
Lemma lem5333232 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333233 : term443 = term293.
Proof. exact (@lem5333232 term157). Qed.
Lemma lem5333234 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333235 : term669 = term663.
Proof. exact (MK_COMB (@lem5333234) (@lem5333233)). Qed.
Lemma lem5333236 : term668 = term431.
Proof. exact (MK_COMB (@lem5333235) (@lem5333230)). Qed.
Lemma lem5333238 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333239 : term431 = term432.
Proof. exact (@lem5333238 (NUMERAL 0) term157). Qed.
Lemma lem5333240 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333241 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333242 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333241 h1) (fun h1 : term432 = True => @lem5333240)). Qed.
Lemma lem5333243 : term432 = True.
Proof. exact (EQ_MP (@lem5333242) (@lem5333240)). Qed.
Lemma lem5333244 : term431 = True.
Proof. exact (TRANS (@lem5333239) (@lem5333243)). Qed.
Lemma lem5333245 : term668 = True.
Proof. exact (TRANS (@lem5333236) (@lem5333244)). Qed.
Lemma lem5333246 : term665 = True.
Proof. exact (TRANS (@lem5333222) (@lem5333245)). Qed.
Lemma lem5333247 : term431 = True.
Proof. exact (TRANS (@lem5333199) (@lem5333246)). Qed.
Lemma lem5333248 : term662 = True.
Proof. exact (TRANS (@lem5333190) (@lem5333247)). Qed.
Lemma lem5333249 : True = term662.
Proof. exact (SYM (@lem5333248)). Qed.
Lemma lem5333250 : term662.
Proof. exact (EQ_MP (@lem5333249) (@lem0)). Qed.
Lemma lem5333251 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term670 _69704 _69707.
Proof. exact (conj (@lem5333250) (@lem5333185 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333253 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5333254 (_69704 : int) (_69707 : int) : term672 _69704 _69707.
Proof. exact (@lem5333253 term305 (term408 _69704 _69707)). Qed.
Lemma lem5333255 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term673 _69704 _69707.
Proof. exact (@lem5333254 _69704 _69707 (@lem5333251 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333256 (_69704 : int) (_69707 : int) : (term674 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (@lem1982733 (term408 _69704 _69707)). Qed.
Lemma lem5333257 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333258 (_69704 : int) (_69707 : int) : (term675 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5333257) (@lem5333256 _69704 _69707)). Qed.
Lemma lem5333259 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333260 (_69704 : int) (_69707 : int) : (term673 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5333258 _69704 _69707) (@lem5333259)). Qed.
Lemma lem5333261 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term411 _69704 _69707.
Proof. exact (EQ_MP (@lem5333260 _69704 _69707) (@lem5333255 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333263 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5333264 : term662 = term431.
Proof. exact (@lem5333263 term293 term305). Qed.
Lemma lem5333266 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333267 : term305 = term397.
Proof. exact (@lem5333266 term157). Qed.
Lemma lem5333269 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333270 : term293 = term352.
Proof. exact (@lem5333269 (NUMERAL 0)). Qed.
Lemma lem5333271 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333272 : term663 = term664.
Proof. exact (MK_COMB (@lem5333271) (@lem5333270)). Qed.
Lemma lem5333273 : term431 = term665.
Proof. exact (MK_COMB (@lem5333272) (@lem5333267)). Qed.
Lemma lem5333274 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5333276 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333277 : term431 = term432.
Proof. exact (@lem5333276 (NUMERAL 0) term157). Qed.
Lemma lem5333278 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333279 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333280 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333279 h1) (fun h1 : term432 = True => @lem5333278)). Qed.
Lemma lem5333281 : term432 = True.
Proof. exact (EQ_MP (@lem5333280) (@lem5333278)). Qed.
Lemma lem5333282 : term431 = True.
Proof. exact (TRANS (@lem5333277) (@lem5333281)). Qed.
Lemma lem5333283 : True = term431.
Proof. exact (SYM (@lem5333282)). Qed.
Lemma lem5333284 : term431.
Proof. exact (EQ_MP (@lem5333283) (@lem0)). Qed.
Lemma lem5333285 : term667.
Proof. exact (@lem5333274 (@lem5333284)). Qed.
Lemma lem5333287 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333288 : term431 = term432.
Proof. exact (@lem5333287 (NUMERAL 0) term157). Qed.
Lemma lem5333289 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333290 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333291 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333290 h1) (fun h1 : term432 = True => @lem5333289)). Qed.
Lemma lem5333292 : term432 = True.
Proof. exact (EQ_MP (@lem5333291) (@lem5333289)). Qed.
Lemma lem5333293 : term431 = True.
Proof. exact (TRANS (@lem5333288) (@lem5333292)). Qed.
Lemma lem5333294 : True = term431.
Proof. exact (SYM (@lem5333293)). Qed.
Lemma lem5333295 : term431.
Proof. exact (EQ_MP (@lem5333294) (@lem0)). Qed.
Lemma lem5333296 : term665 = term668.
Proof. exact (@lem5333285 (@lem5333295)). Qed.
Lemma lem5333298 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333299 : term364 = term365.
Proof. exact (@lem5333298 term157 term157). Qed.
Lemma lem5333300 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333301 : term367 = term157.
Proof. exact (EQ_MP (@lem5333300) (@lem940073)). Qed.
Lemma lem5333302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333303 : term365 = term305.
Proof. exact (MK_COMB (@lem5333302) (@lem5333301)). Qed.
Lemma lem5333304 : term364 = term305.
Proof. exact (TRANS (@lem5333299) (@lem5333303)). Qed.
Lemma lem5333306 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333307 : term443 = term293.
Proof. exact (@lem5333306 term157). Qed.
Lemma lem5333308 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333309 : term669 = term663.
Proof. exact (MK_COMB (@lem5333308) (@lem5333307)). Qed.
Lemma lem5333310 : term668 = term431.
Proof. exact (MK_COMB (@lem5333309) (@lem5333304)). Qed.
Lemma lem5333312 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333313 : term431 = term432.
Proof. exact (@lem5333312 (NUMERAL 0) term157). Qed.
Lemma lem5333314 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333315 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333316 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333315 h1) (fun h1 : term432 = True => @lem5333314)). Qed.
Lemma lem5333317 : term432 = True.
Proof. exact (EQ_MP (@lem5333316) (@lem5333314)). Qed.
Lemma lem5333318 : term431 = True.
Proof. exact (TRANS (@lem5333313) (@lem5333317)). Qed.
Lemma lem5333319 : term668 = True.
Proof. exact (TRANS (@lem5333310) (@lem5333318)). Qed.
Lemma lem5333320 : term665 = True.
Proof. exact (TRANS (@lem5333296) (@lem5333319)). Qed.
Lemma lem5333321 : term431 = True.
Proof. exact (TRANS (@lem5333273) (@lem5333320)). Qed.
Lemma lem5333322 : term662 = True.
Proof. exact (TRANS (@lem5333264) (@lem5333321)). Qed.
Lemma lem5333323 : True = term662.
Proof. exact (SYM (@lem5333322)). Qed.
Lemma lem5333324 : term662.
Proof. exact (EQ_MP (@lem5333323) (@lem0)). Qed.
Lemma lem5333325 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term676 _69704 _69707.
Proof. exact (conj (@lem5333324) (@lem5333187 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333327 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5333328 (_69704 : int) (_69707 : int) : term677 _69704 _69707.
Proof. exact (@lem5333327 term305 (term452 _69704 _69707)). Qed.
Lemma lem5333329 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term678 _69704 _69707.
Proof. exact (@lem5333328 _69704 _69707 (@lem5333325 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333330 (_69704 : int) (_69707 : int) : (term679 _69704 _69707) = (term452 _69704 _69707).
Proof. exact (@lem1982733 (term452 _69704 _69707)). Qed.
Lemma lem5333331 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333332 (_69704 : int) (_69707 : int) : (term680 _69704 _69707) = (term453 _69704 _69707).
Proof. exact (MK_COMB (@lem5333331) (@lem5333330 _69704 _69707)). Qed.
Lemma lem5333333 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333334 (_69704 : int) (_69707 : int) : (term678 _69704 _69707) = (term454 _69704 _69707).
Proof. exact (MK_COMB (@lem5333332 _69704 _69707) (@lem5333333)). Qed.
Lemma lem5333335 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term454 _69704 _69707.
Proof. exact (EQ_MP (@lem5333334 _69704 _69707) (@lem5333329 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333336 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term681 _69704 _69707.
Proof. exact (conj (@lem5333335 _69706 _69704 _69705 _69707 h1) (@lem5333261 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333338 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5333339 (_69704 : int) (_69707 : int) : term683 _69704 _69707.
Proof. exact (@lem5333338 (term452 _69704 _69707) (term408 _69704 _69707)). Qed.
Lemma lem5333340 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term684 _69704 _69707.
Proof. exact (@lem5333339 _69704 _69707 (@lem5333336 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333341 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = (term686 _69704 _69707).
Proof. exact (@lem1982753 (term380 _69704) (real_of_int _69704) (real_of_int _69707) (term407 _69707)). Qed.
Lemma lem5333342 (_69704 : int) : (term687 _69704) = (term688 _69704).
Proof. exact (@lem1982713 term355 (real_of_int _69704)). Qed.
Lemma lem5333344 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333345 : term305 = term397.
Proof. exact (@lem5333344 term157). Qed.
Lemma lem5333347 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333348 : term355 = term356.
Proof. exact (@lem5333347 term157). Qed.
Lemma lem5333349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333350 : term689 = term690.
Proof. exact (MK_COMB (@lem5333349) (@lem5333348)). Qed.
Lemma lem5333351 : term691 = term692.
Proof. exact (MK_COMB (@lem5333350) (@lem5333345)). Qed.
Lemma lem5333352 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5333354 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333355 : term431 = term432.
Proof. exact (@lem5333354 (NUMERAL 0) term157). Qed.
Lemma lem5333356 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333357 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333358 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333357 h1) (fun h1 : term432 = True => @lem5333356)). Qed.
Lemma lem5333359 : term432 = True.
Proof. exact (EQ_MP (@lem5333358) (@lem5333356)). Qed.
Lemma lem5333360 : term431 = True.
Proof. exact (TRANS (@lem5333355) (@lem5333359)). Qed.
Lemma lem5333361 : True = term431.
Proof. exact (SYM (@lem5333360)). Qed.
Lemma lem5333362 : term431.
Proof. exact (EQ_MP (@lem5333361) (@lem0)). Qed.
Lemma lem5333363 : term694.
Proof. exact (@lem5333352 (@lem5333362)). Qed.
Lemma lem5333365 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333366 : term431 = term432.
Proof. exact (@lem5333365 (NUMERAL 0) term157). Qed.
Lemma lem5333367 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333368 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333369 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333368 h1) (fun h1 : term432 = True => @lem5333367)). Qed.
Lemma lem5333370 : term432 = True.
Proof. exact (EQ_MP (@lem5333369) (@lem5333367)). Qed.
Lemma lem5333371 : term431 = True.
Proof. exact (TRANS (@lem5333366) (@lem5333370)). Qed.
Lemma lem5333372 : True = term431.
Proof. exact (SYM (@lem5333371)). Qed.
Lemma lem5333373 : term431.
Proof. exact (EQ_MP (@lem5333372) (@lem0)). Qed.
Lemma lem5333374 : term695.
Proof. exact (@lem5333363 (@lem5333373)). Qed.
Lemma lem5333376 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333377 : term431 = term432.
Proof. exact (@lem5333376 (NUMERAL 0) term157). Qed.
Lemma lem5333378 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333379 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333380 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333379 h1) (fun h1 : term432 = True => @lem5333378)). Qed.
Lemma lem5333381 : term432 = True.
Proof. exact (EQ_MP (@lem5333380) (@lem5333378)). Qed.
Lemma lem5333382 : term431 = True.
Proof. exact (TRANS (@lem5333377) (@lem5333381)). Qed.
Lemma lem5333383 : True = term431.
Proof. exact (SYM (@lem5333382)). Qed.
Lemma lem5333384 : term431.
Proof. exact (EQ_MP (@lem5333383) (@lem0)). Qed.
Lemma lem5333385 : term696.
Proof. exact (@lem5333374 (@lem5333384)). Qed.
Lemma lem5333387 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333388 : term364 = term365.
Proof. exact (@lem5333387 term157 term157). Qed.
Lemma lem5333389 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333390 : term367 = term157.
Proof. exact (EQ_MP (@lem5333389) (@lem940073)). Qed.
Lemma lem5333391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333392 : term365 = term305.
Proof. exact (MK_COMB (@lem5333391) (@lem5333390)). Qed.
Lemma lem5333393 : term364 = term305.
Proof. exact (TRANS (@lem5333388) (@lem5333392)). Qed.
Lemma lem5333395 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333396 : term398 = term403.
Proof. exact (@lem5333395 term157 term157). Qed.
Lemma lem5333397 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333398 : term367 = term157.
Proof. exact (EQ_MP (@lem5333397) (@lem940073)). Qed.
Lemma lem5333399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333400 : term365 = term305.
Proof. exact (MK_COMB (@lem5333399) (@lem5333398)). Qed.
Lemma lem5333401 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333402 : term403 = term355.
Proof. exact (MK_COMB (@lem5333401) (@lem5333400)). Qed.
Lemma lem5333403 : term398 = term355.
Proof. exact (TRANS (@lem5333396) (@lem5333402)). Qed.
Lemma lem5333404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333405 : term697 = term689.
Proof. exact (MK_COMB (@lem5333404) (@lem5333403)). Qed.
Lemma lem5333406 : term698 = term691.
Proof. exact (MK_COMB (@lem5333405) (@lem5333393)). Qed.
Lemma lem5333408 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5333409 : term691 = term293.
Proof. exact (@lem5333408 term157). Qed.
Lemma lem5333410 : term698 = term293.
Proof. exact (TRANS (@lem5333406) (@lem5333409)). Qed.
Lemma lem5333411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333412 : term700 = term441.
Proof. exact (MK_COMB (@lem5333411) (@lem5333410)). Qed.
Lemma lem5333413 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5333414 : term701 = term443.
Proof. exact (MK_COMB (@lem5333412) (@lem5333413)). Qed.
Lemma lem5333416 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333417 : term443 = term293.
Proof. exact (@lem5333416 term157). Qed.
Lemma lem5333418 : term701 = term293.
Proof. exact (TRANS (@lem5333414) (@lem5333417)). Qed.
Lemma lem5333420 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333421 : term364 = term365.
Proof. exact (@lem5333420 term157 term157). Qed.
Lemma lem5333422 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333423 : term367 = term157.
Proof. exact (EQ_MP (@lem5333422) (@lem940073)). Qed.
Lemma lem5333424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333425 : term365 = term305.
Proof. exact (MK_COMB (@lem5333424) (@lem5333423)). Qed.
Lemma lem5333426 : term364 = term305.
Proof. exact (TRANS (@lem5333421) (@lem5333425)). Qed.
Lemma lem5333427 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5333428 : term445 = term443.
Proof. exact (MK_COMB (@lem5333427) (@lem5333426)). Qed.
Lemma lem5333430 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333431 : term443 = term293.
Proof. exact (@lem5333430 term157). Qed.
Lemma lem5333432 : term445 = term293.
Proof. exact (TRANS (@lem5333428) (@lem5333431)). Qed.
Lemma lem5333433 : term293 = term445.
Proof. exact (SYM (@lem5333432)). Qed.
Lemma lem5333434 : term701 = term445.
Proof. exact (TRANS (@lem5333418) (@lem5333433)). Qed.
Lemma lem5333435 : term692 = term352.
Proof. exact (@lem5333385 (@lem5333434)). Qed.
Lemma lem5333436 : term691 = term352.
Proof. exact (TRANS (@lem5333351) (@lem5333435)). Qed.
Lemma lem5333438 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5333439 : term352 = term293.
Proof. exact (@lem5333438 term293). Qed.
Lemma lem5333440 : term691 = term293.
Proof. exact (TRANS (@lem5333436) (@lem5333439)). Qed.
Lemma lem5333441 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333442 : term702 = term441.
Proof. exact (MK_COMB (@lem5333441) (@lem5333440)). Qed.
Lemma lem5333443 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5333444 (_69704 : int) : (term688 _69704) = (term703 _69704).
Proof. exact (MK_COMB (@lem5333442) (@lem5333443 _69704)). Qed.
Lemma lem5333445 (_69704 : int) : (term687 _69704) = (term703 _69704).
Proof. exact (TRANS (@lem5333342 _69704) (@lem5333444 _69704)). Qed.
Lemma lem5333446 (_69704 : int) : (term703 _69704) = term293.
Proof. exact (@lem1982719 (real_of_int _69704)). Qed.
Lemma lem5333447 (_69704 : int) : (term687 _69704) = term293.
Proof. exact (TRANS (@lem5333445 _69704) (@lem5333446 _69704)). Qed.
Lemma lem5333448 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333449 (_69704 : int) : (term704 _69704) = term705.
Proof. exact (MK_COMB (@lem5333448) (@lem5333447 _69704)). Qed.
Lemma lem5333450 (_69707 : int) : (term706 _69707) = (term707 _69707).
Proof. exact (@lem1982763 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5333451 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5333453 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333454 : term305 = term397.
Proof. exact (@lem5333453 term157). Qed.
Lemma lem5333456 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333457 : term355 = term356.
Proof. exact (@lem5333456 term157). Qed.
Lemma lem5333458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333459 : term689 = term690.
Proof. exact (MK_COMB (@lem5333458) (@lem5333457)). Qed.
Lemma lem5333460 : term691 = term692.
Proof. exact (MK_COMB (@lem5333459) (@lem5333454)). Qed.
Lemma lem5333461 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5333463 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333464 : term431 = term432.
Proof. exact (@lem5333463 (NUMERAL 0) term157). Qed.
Lemma lem5333465 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333466 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333467 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333466 h1) (fun h1 : term432 = True => @lem5333465)). Qed.
Lemma lem5333468 : term432 = True.
Proof. exact (EQ_MP (@lem5333467) (@lem5333465)). Qed.
Lemma lem5333469 : term431 = True.
Proof. exact (TRANS (@lem5333464) (@lem5333468)). Qed.
Lemma lem5333470 : True = term431.
Proof. exact (SYM (@lem5333469)). Qed.
Lemma lem5333471 : term431.
Proof. exact (EQ_MP (@lem5333470) (@lem0)). Qed.
Lemma lem5333472 : term694.
Proof. exact (@lem5333461 (@lem5333471)). Qed.
Lemma lem5333474 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333475 : term431 = term432.
Proof. exact (@lem5333474 (NUMERAL 0) term157). Qed.
Lemma lem5333476 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333477 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333478 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333477 h1) (fun h1 : term432 = True => @lem5333476)). Qed.
Lemma lem5333479 : term432 = True.
Proof. exact (EQ_MP (@lem5333478) (@lem5333476)). Qed.
Lemma lem5333480 : term431 = True.
Proof. exact (TRANS (@lem5333475) (@lem5333479)). Qed.
Lemma lem5333481 : True = term431.
Proof. exact (SYM (@lem5333480)). Qed.
Lemma lem5333482 : term431.
Proof. exact (EQ_MP (@lem5333481) (@lem0)). Qed.
Lemma lem5333483 : term695.
Proof. exact (@lem5333472 (@lem5333482)). Qed.
Lemma lem5333485 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333486 : term431 = term432.
Proof. exact (@lem5333485 (NUMERAL 0) term157). Qed.
Lemma lem5333487 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333488 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333489 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333488 h1) (fun h1 : term432 = True => @lem5333487)). Qed.
Lemma lem5333490 : term432 = True.
Proof. exact (EQ_MP (@lem5333489) (@lem5333487)). Qed.
Lemma lem5333491 : term431 = True.
Proof. exact (TRANS (@lem5333486) (@lem5333490)). Qed.
Lemma lem5333492 : True = term431.
Proof. exact (SYM (@lem5333491)). Qed.
Lemma lem5333493 : term431.
Proof. exact (EQ_MP (@lem5333492) (@lem0)). Qed.
Lemma lem5333494 : term696.
Proof. exact (@lem5333483 (@lem5333493)). Qed.
Lemma lem5333496 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333497 : term364 = term365.
Proof. exact (@lem5333496 term157 term157). Qed.
Lemma lem5333498 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333499 : term367 = term157.
Proof. exact (EQ_MP (@lem5333498) (@lem940073)). Qed.
Lemma lem5333500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333501 : term365 = term305.
Proof. exact (MK_COMB (@lem5333500) (@lem5333499)). Qed.
Lemma lem5333502 : term364 = term305.
Proof. exact (TRANS (@lem5333497) (@lem5333501)). Qed.
Lemma lem5333504 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333505 : term398 = term403.
Proof. exact (@lem5333504 term157 term157). Qed.
Lemma lem5333506 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333507 : term367 = term157.
Proof. exact (EQ_MP (@lem5333506) (@lem940073)). Qed.
Lemma lem5333508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333509 : term365 = term305.
Proof. exact (MK_COMB (@lem5333508) (@lem5333507)). Qed.
Lemma lem5333510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333511 : term403 = term355.
Proof. exact (MK_COMB (@lem5333510) (@lem5333509)). Qed.
Lemma lem5333512 : term398 = term355.
Proof. exact (TRANS (@lem5333505) (@lem5333511)). Qed.
Lemma lem5333513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333514 : term697 = term689.
Proof. exact (MK_COMB (@lem5333513) (@lem5333512)). Qed.
Lemma lem5333515 : term698 = term691.
Proof. exact (MK_COMB (@lem5333514) (@lem5333502)). Qed.
Lemma lem5333517 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5333518 : term691 = term293.
Proof. exact (@lem5333517 term157). Qed.
Lemma lem5333519 : term698 = term293.
Proof. exact (TRANS (@lem5333515) (@lem5333518)). Qed.
Lemma lem5333520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333521 : term700 = term441.
Proof. exact (MK_COMB (@lem5333520) (@lem5333519)). Qed.
Lemma lem5333522 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5333523 : term701 = term443.
Proof. exact (MK_COMB (@lem5333521) (@lem5333522)). Qed.
Lemma lem5333525 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333526 : term443 = term293.
Proof. exact (@lem5333525 term157). Qed.
Lemma lem5333527 : term701 = term293.
Proof. exact (TRANS (@lem5333523) (@lem5333526)). Qed.
Lemma lem5333529 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333530 : term364 = term365.
Proof. exact (@lem5333529 term157 term157). Qed.
Lemma lem5333531 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333532 : term367 = term157.
Proof. exact (EQ_MP (@lem5333531) (@lem940073)). Qed.
Lemma lem5333533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333534 : term365 = term305.
Proof. exact (MK_COMB (@lem5333533) (@lem5333532)). Qed.
Lemma lem5333535 : term364 = term305.
Proof. exact (TRANS (@lem5333530) (@lem5333534)). Qed.
Lemma lem5333536 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5333537 : term445 = term443.
Proof. exact (MK_COMB (@lem5333536) (@lem5333535)). Qed.
Lemma lem5333539 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333540 : term443 = term293.
Proof. exact (@lem5333539 term157). Qed.
Lemma lem5333541 : term445 = term293.
Proof. exact (TRANS (@lem5333537) (@lem5333540)). Qed.
Lemma lem5333542 : term293 = term445.
Proof. exact (SYM (@lem5333541)). Qed.
Lemma lem5333543 : term701 = term445.
Proof. exact (TRANS (@lem5333527) (@lem5333542)). Qed.
Lemma lem5333544 : term692 = term352.
Proof. exact (@lem5333494 (@lem5333543)). Qed.
Lemma lem5333545 : term691 = term352.
Proof. exact (TRANS (@lem5333460) (@lem5333544)). Qed.
Lemma lem5333547 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5333548 : term352 = term293.
Proof. exact (@lem5333547 term293). Qed.
Lemma lem5333549 : term691 = term293.
Proof. exact (TRANS (@lem5333545) (@lem5333548)). Qed.
Lemma lem5333550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333551 : term702 = term441.
Proof. exact (MK_COMB (@lem5333550) (@lem5333549)). Qed.
Lemma lem5333552 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5333553 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5333551) (@lem5333552 _69707)). Qed.
Lemma lem5333554 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5333451 _69707) (@lem5333553 _69707)). Qed.
Lemma lem5333555 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5333556 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5333554 _69707) (@lem5333555 _69707)). Qed.
Lemma lem5333557 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333558 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5333557) (@lem5333556 _69707)). Qed.
Lemma lem5333559 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5333560 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5333558 _69707) (@lem5333559)). Qed.
Lemma lem5333561 (_69707 : int) : (term706 _69707) = term710.
Proof. exact (TRANS (@lem5333450 _69707) (@lem5333560 _69707)). Qed.
Lemma lem5333562 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5333563 (_69707 : int) : (term706 _69707) = term355.
Proof. exact (TRANS (@lem5333561 _69707) (@lem5333562)). Qed.
Lemma lem5333564 (_69704 : int) (_69707 : int) : (term686 _69704 _69707) = term710.
Proof. exact (MK_COMB (@lem5333449 _69704) (@lem5333563 _69707)). Qed.
Lemma lem5333565 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term710.
Proof. exact (TRANS (@lem5333341 _69704 _69707) (@lem5333564 _69704 _69707)). Qed.
Lemma lem5333566 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5333567 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term355.
Proof. exact (TRANS (@lem5333565 _69704 _69707) (@lem5333566)). Qed.
Lemma lem5333568 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333569 (_69704 : int) (_69707 : int) : (term711 _69704 _69707) = term712.
Proof. exact (MK_COMB (@lem5333568) (@lem5333567 _69704 _69707)). Qed.
Lemma lem5333570 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333571 (_69704 : int) (_69707 : int) : (term684 _69704 _69707) = term713.
Proof. exact (MK_COMB (@lem5333569 _69704 _69707) (@lem5333570)). Qed.
Lemma lem5333572 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5333571 _69704 _69707) (@lem5333340 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333574 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5333575 : term713 = term714.
Proof. exact (@lem5333574 term293 term355). Qed.
Lemma lem5333577 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333578 : term355 = term356.
Proof. exact (@lem5333577 term157). Qed.
Lemma lem5333580 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333581 : term293 = term352.
Proof. exact (@lem5333580 (NUMERAL 0)). Qed.
Lemma lem5333582 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5333583 : term295 = term715.
Proof. exact (MK_COMB (@lem5333582) (@lem5333581)). Qed.
Lemma lem5333584 : term714 = term716.
Proof. exact (MK_COMB (@lem5333583) (@lem5333578)). Qed.
Lemma lem5333585 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5333587 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333588 : term431 = term432.
Proof. exact (@lem5333587 (NUMERAL 0) term157). Qed.
Lemma lem5333589 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333590 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333591 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333590 h1) (fun h1 : term432 = True => @lem5333589)). Qed.
Lemma lem5333592 : term432 = True.
Proof. exact (EQ_MP (@lem5333591) (@lem5333589)). Qed.
Lemma lem5333593 : term431 = True.
Proof. exact (TRANS (@lem5333588) (@lem5333592)). Qed.
Lemma lem5333594 : True = term431.
Proof. exact (SYM (@lem5333593)). Qed.
Lemma lem5333595 : term431.
Proof. exact (EQ_MP (@lem5333594) (@lem0)). Qed.
Lemma lem5333596 : term718.
Proof. exact (@lem5333585 (@lem5333595)). Qed.
Lemma lem5333598 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333599 : term431 = term432.
Proof. exact (@lem5333598 (NUMERAL 0) term157). Qed.
Lemma lem5333600 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333601 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333602 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333601 h1) (fun h1 : term432 = True => @lem5333600)). Qed.
Lemma lem5333603 : term432 = True.
Proof. exact (EQ_MP (@lem5333602) (@lem5333600)). Qed.
Lemma lem5333604 : term431 = True.
Proof. exact (TRANS (@lem5333599) (@lem5333603)). Qed.
Lemma lem5333605 : True = term431.
Proof. exact (SYM (@lem5333604)). Qed.
Lemma lem5333606 : term431.
Proof. exact (EQ_MP (@lem5333605) (@lem0)). Qed.
Lemma lem5333607 : term716 = term719.
Proof. exact (@lem5333596 (@lem5333606)). Qed.
Lemma lem5333609 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333610 : term398 = term403.
Proof. exact (@lem5333609 term157 term157). Qed.
Lemma lem5333611 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333612 : term367 = term157.
Proof. exact (EQ_MP (@lem5333611) (@lem940073)). Qed.
Lemma lem5333613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333614 : term365 = term305.
Proof. exact (MK_COMB (@lem5333613) (@lem5333612)). Qed.
Lemma lem5333615 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333616 : term403 = term355.
Proof. exact (MK_COMB (@lem5333615) (@lem5333614)). Qed.
Lemma lem5333617 : term398 = term355.
Proof. exact (TRANS (@lem5333610) (@lem5333616)). Qed.
Lemma lem5333619 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333620 : term443 = term293.
Proof. exact (@lem5333619 term157). Qed.
Lemma lem5333621 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5333622 : term720 = term295.
Proof. exact (MK_COMB (@lem5333621) (@lem5333620)). Qed.
Lemma lem5333623 : term719 = term714.
Proof. exact (MK_COMB (@lem5333622) (@lem5333617)). Qed.
Lemma lem5333625 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5333626 : term714 = term723.
Proof. exact (@lem5333625 (NUMERAL 0) term157). Qed.
Lemma lem5333627 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333628 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5333629 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333628 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5333627)). Qed.
Lemma lem5333630 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5333629) (@lem5333627)). Qed.
Lemma lem5333631 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5333632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5333633 : term724 = (and True).
Proof. exact (MK_COMB (@lem5333632) (@lem5333631)). Qed.
Lemma lem5333634 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5333633) (@lem5333630)). Qed.
Lemma lem5333636 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5333637 : term723 = False.
Proof. exact (TRANS (@lem5333634) (@lem5333636)). Qed.
Lemma lem5333638 : term714 = False.
Proof. exact (TRANS (@lem5333626) (@lem5333637)). Qed.
Lemma lem5333639 : term719 = False.
Proof. exact (TRANS (@lem5333623) (@lem5333638)). Qed.
Lemma lem5333640 : term716 = False.
Proof. exact (TRANS (@lem5333607) (@lem5333639)). Qed.
Lemma lem5333641 : term714 = False.
Proof. exact (TRANS (@lem5333584) (@lem5333640)). Qed.
Lemma lem5333642 : term713 = False.
Proof. exact (TRANS (@lem5333575) (@lem5333641)). Qed.
Lemma lem5333643 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term743 _69706 _69704 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5333642) (@lem5333572 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333644 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term744 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5333645 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term650 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333644 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333647 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term619 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333645 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333649 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term588 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333647 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333651 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term557 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333649 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333653 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term526 _69706 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333651 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333657 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term456 _69704 _69705 _69707.
Proof. exact (proj2 (@lem5333653 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333658 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term496 _69706 _69705 _69707.
Proof. exact (proj1 (@lem5333653 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333659 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term414 _69705 _69707.
Proof. exact (proj2 (@lem5333658 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333661 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term389 _69705 _69707.
Proof. exact (proj2 (@lem5333657 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333664 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5333665 : term662 = term431.
Proof. exact (@lem5333664 term293 term305). Qed.
Lemma lem5333667 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333668 : term305 = term397.
Proof. exact (@lem5333667 term157). Qed.
Lemma lem5333670 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333671 : term293 = term352.
Proof. exact (@lem5333670 (NUMERAL 0)). Qed.
Lemma lem5333672 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333673 : term663 = term664.
Proof. exact (MK_COMB (@lem5333672) (@lem5333671)). Qed.
Lemma lem5333674 : term431 = term665.
Proof. exact (MK_COMB (@lem5333673) (@lem5333668)). Qed.
Lemma lem5333675 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5333677 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333678 : term431 = term432.
Proof. exact (@lem5333677 (NUMERAL 0) term157). Qed.
Lemma lem5333679 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333680 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333681 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333680 h1) (fun h1 : term432 = True => @lem5333679)). Qed.
Lemma lem5333682 : term432 = True.
Proof. exact (EQ_MP (@lem5333681) (@lem5333679)). Qed.
Lemma lem5333683 : term431 = True.
Proof. exact (TRANS (@lem5333678) (@lem5333682)). Qed.
Lemma lem5333684 : True = term431.
Proof. exact (SYM (@lem5333683)). Qed.
Lemma lem5333685 : term431.
Proof. exact (EQ_MP (@lem5333684) (@lem0)). Qed.
Lemma lem5333686 : term667.
Proof. exact (@lem5333675 (@lem5333685)). Qed.
Lemma lem5333688 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333689 : term431 = term432.
Proof. exact (@lem5333688 (NUMERAL 0) term157). Qed.
Lemma lem5333690 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333691 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333692 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333691 h1) (fun h1 : term432 = True => @lem5333690)). Qed.
Lemma lem5333693 : term432 = True.
Proof. exact (EQ_MP (@lem5333692) (@lem5333690)). Qed.
Lemma lem5333694 : term431 = True.
Proof. exact (TRANS (@lem5333689) (@lem5333693)). Qed.
Lemma lem5333695 : True = term431.
Proof. exact (SYM (@lem5333694)). Qed.
Lemma lem5333696 : term431.
Proof. exact (EQ_MP (@lem5333695) (@lem0)). Qed.
Lemma lem5333697 : term665 = term668.
Proof. exact (@lem5333686 (@lem5333696)). Qed.
Lemma lem5333699 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333700 : term364 = term365.
Proof. exact (@lem5333699 term157 term157). Qed.
Lemma lem5333701 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333702 : term367 = term157.
Proof. exact (EQ_MP (@lem5333701) (@lem940073)). Qed.
Lemma lem5333703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333704 : term365 = term305.
Proof. exact (MK_COMB (@lem5333703) (@lem5333702)). Qed.
Lemma lem5333705 : term364 = term305.
Proof. exact (TRANS (@lem5333700) (@lem5333704)). Qed.
Lemma lem5333707 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333708 : term443 = term293.
Proof. exact (@lem5333707 term157). Qed.
Lemma lem5333709 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333710 : term669 = term663.
Proof. exact (MK_COMB (@lem5333709) (@lem5333708)). Qed.
Lemma lem5333711 : term668 = term431.
Proof. exact (MK_COMB (@lem5333710) (@lem5333705)). Qed.
Lemma lem5333713 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333714 : term431 = term432.
Proof. exact (@lem5333713 (NUMERAL 0) term157). Qed.
Lemma lem5333715 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333716 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333717 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333716 h1) (fun h1 : term432 = True => @lem5333715)). Qed.
Lemma lem5333718 : term432 = True.
Proof. exact (EQ_MP (@lem5333717) (@lem5333715)). Qed.
Lemma lem5333719 : term431 = True.
Proof. exact (TRANS (@lem5333714) (@lem5333718)). Qed.
Lemma lem5333720 : term668 = True.
Proof. exact (TRANS (@lem5333711) (@lem5333719)). Qed.
Lemma lem5333721 : term665 = True.
Proof. exact (TRANS (@lem5333697) (@lem5333720)). Qed.
Lemma lem5333722 : term431 = True.
Proof. exact (TRANS (@lem5333674) (@lem5333721)). Qed.
Lemma lem5333723 : term662 = True.
Proof. exact (TRANS (@lem5333665) (@lem5333722)). Qed.
Lemma lem5333724 : True = term662.
Proof. exact (SYM (@lem5333723)). Qed.
Lemma lem5333725 : term662.
Proof. exact (EQ_MP (@lem5333724) (@lem0)). Qed.
Lemma lem5333726 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term726 _69705 _69707.
Proof. exact (conj (@lem5333725) (@lem5333661 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333728 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5333729 (_69705 : int) (_69707 : int) : term727 _69705 _69707.
Proof. exact (@lem5333728 term305 (term386 _69705 _69707)). Qed.
Lemma lem5333730 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term728 _69705 _69707.
Proof. exact (@lem5333729 _69705 _69707 (@lem5333726 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333731 (_69705 : int) (_69707 : int) : (term729 _69705 _69707) = (term386 _69705 _69707).
Proof. exact (@lem1982733 (term386 _69705 _69707)). Qed.
Lemma lem5333732 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333733 (_69705 : int) (_69707 : int) : (term730 _69705 _69707) = (term388 _69705 _69707).
Proof. exact (MK_COMB (@lem5333732) (@lem5333731 _69705 _69707)). Qed.
Lemma lem5333734 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333735 (_69705 : int) (_69707 : int) : (term728 _69705 _69707) = (term389 _69705 _69707).
Proof. exact (MK_COMB (@lem5333733 _69705 _69707) (@lem5333734)). Qed.
Lemma lem5333736 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term389 _69705 _69707.
Proof. exact (EQ_MP (@lem5333735 _69705 _69707) (@lem5333730 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333738 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5333739 : term662 = term431.
Proof. exact (@lem5333738 term293 term305). Qed.
Lemma lem5333741 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333742 : term305 = term397.
Proof. exact (@lem5333741 term157). Qed.
Lemma lem5333744 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333745 : term293 = term352.
Proof. exact (@lem5333744 (NUMERAL 0)). Qed.
Lemma lem5333746 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333747 : term663 = term664.
Proof. exact (MK_COMB (@lem5333746) (@lem5333745)). Qed.
Lemma lem5333748 : term431 = term665.
Proof. exact (MK_COMB (@lem5333747) (@lem5333742)). Qed.
Lemma lem5333749 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5333751 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333752 : term431 = term432.
Proof. exact (@lem5333751 (NUMERAL 0) term157). Qed.
Lemma lem5333753 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333754 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333755 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333754 h1) (fun h1 : term432 = True => @lem5333753)). Qed.
Lemma lem5333756 : term432 = True.
Proof. exact (EQ_MP (@lem5333755) (@lem5333753)). Qed.
Lemma lem5333757 : term431 = True.
Proof. exact (TRANS (@lem5333752) (@lem5333756)). Qed.
Lemma lem5333758 : True = term431.
Proof. exact (SYM (@lem5333757)). Qed.
Lemma lem5333759 : term431.
Proof. exact (EQ_MP (@lem5333758) (@lem0)). Qed.
Lemma lem5333760 : term667.
Proof. exact (@lem5333749 (@lem5333759)). Qed.
Lemma lem5333762 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333763 : term431 = term432.
Proof. exact (@lem5333762 (NUMERAL 0) term157). Qed.
Lemma lem5333764 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333765 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333766 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333765 h1) (fun h1 : term432 = True => @lem5333764)). Qed.
Lemma lem5333767 : term432 = True.
Proof. exact (EQ_MP (@lem5333766) (@lem5333764)). Qed.
Lemma lem5333768 : term431 = True.
Proof. exact (TRANS (@lem5333763) (@lem5333767)). Qed.
Lemma lem5333769 : True = term431.
Proof. exact (SYM (@lem5333768)). Qed.
Lemma lem5333770 : term431.
Proof. exact (EQ_MP (@lem5333769) (@lem0)). Qed.
Lemma lem5333771 : term665 = term668.
Proof. exact (@lem5333760 (@lem5333770)). Qed.
Lemma lem5333773 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333774 : term364 = term365.
Proof. exact (@lem5333773 term157 term157). Qed.
Lemma lem5333775 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333776 : term367 = term157.
Proof. exact (EQ_MP (@lem5333775) (@lem940073)). Qed.
Lemma lem5333777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333778 : term365 = term305.
Proof. exact (MK_COMB (@lem5333777) (@lem5333776)). Qed.
Lemma lem5333779 : term364 = term305.
Proof. exact (TRANS (@lem5333774) (@lem5333778)). Qed.
Lemma lem5333781 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333782 : term443 = term293.
Proof. exact (@lem5333781 term157). Qed.
Lemma lem5333783 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5333784 : term669 = term663.
Proof. exact (MK_COMB (@lem5333783) (@lem5333782)). Qed.
Lemma lem5333785 : term668 = term431.
Proof. exact (MK_COMB (@lem5333784) (@lem5333779)). Qed.
Lemma lem5333787 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333788 : term431 = term432.
Proof. exact (@lem5333787 (NUMERAL 0) term157). Qed.
Lemma lem5333789 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333790 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333791 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333790 h1) (fun h1 : term432 = True => @lem5333789)). Qed.
Lemma lem5333792 : term432 = True.
Proof. exact (EQ_MP (@lem5333791) (@lem5333789)). Qed.
Lemma lem5333793 : term431 = True.
Proof. exact (TRANS (@lem5333788) (@lem5333792)). Qed.
Lemma lem5333794 : term668 = True.
Proof. exact (TRANS (@lem5333785) (@lem5333793)). Qed.
Lemma lem5333795 : term665 = True.
Proof. exact (TRANS (@lem5333771) (@lem5333794)). Qed.
Lemma lem5333796 : term431 = True.
Proof. exact (TRANS (@lem5333748) (@lem5333795)). Qed.
Lemma lem5333797 : term662 = True.
Proof. exact (TRANS (@lem5333739) (@lem5333796)). Qed.
Lemma lem5333798 : True = term662.
Proof. exact (SYM (@lem5333797)). Qed.
Lemma lem5333799 : term662.
Proof. exact (EQ_MP (@lem5333798) (@lem0)). Qed.
Lemma lem5333800 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term731 _69705 _69707.
Proof. exact (conj (@lem5333799) (@lem5333659 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333802 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5333803 (_69705 : int) (_69707 : int) : term732 _69705 _69707.
Proof. exact (@lem5333802 term305 (term412 _69705 _69707)). Qed.
Lemma lem5333804 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term733 _69705 _69707.
Proof. exact (@lem5333803 _69705 _69707 (@lem5333800 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333805 (_69705 : int) (_69707 : int) : (term734 _69705 _69707) = (term412 _69705 _69707).
Proof. exact (@lem1982733 (term412 _69705 _69707)). Qed.
Lemma lem5333806 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5333807 (_69705 : int) (_69707 : int) : (term735 _69705 _69707) = (term413 _69705 _69707).
Proof. exact (MK_COMB (@lem5333806) (@lem5333805 _69705 _69707)). Qed.
Lemma lem5333808 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5333809 (_69705 : int) (_69707 : int) : (term733 _69705 _69707) = (term414 _69705 _69707).
Proof. exact (MK_COMB (@lem5333807 _69705 _69707) (@lem5333808)). Qed.
Lemma lem5333810 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term414 _69705 _69707.
Proof. exact (EQ_MP (@lem5333809 _69705 _69707) (@lem5333804 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333811 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term500 _69705 _69707.
Proof. exact (conj (@lem5333810 _69706 _69704 _69705 _69707 h1) (@lem5333736 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333813 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5333814 (_69705 : int) (_69707 : int) : term736 _69705 _69707.
Proof. exact (@lem5333813 (term412 _69705 _69707) (term386 _69705 _69707)). Qed.
Lemma lem5333815 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term737 _69705 _69707.
Proof. exact (@lem5333814 _69705 _69707 (@lem5333811 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5333816 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = (term739 _69705 _69707).
Proof. exact (@lem1982753 (term380 _69705) (real_of_int _69705) (term740 _69707) (term380 _69707)). Qed.
Lemma lem5333817 (_69705 : int) : (term687 _69705) = (term688 _69705).
Proof. exact (@lem1982713 term355 (real_of_int _69705)). Qed.
Lemma lem5333819 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333820 : term305 = term397.
Proof. exact (@lem5333819 term157). Qed.
Lemma lem5333822 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333823 : term355 = term356.
Proof. exact (@lem5333822 term157). Qed.
Lemma lem5333824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333825 : term689 = term690.
Proof. exact (MK_COMB (@lem5333824) (@lem5333823)). Qed.
Lemma lem5333826 : term691 = term692.
Proof. exact (MK_COMB (@lem5333825) (@lem5333820)). Qed.
Lemma lem5333827 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5333829 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333830 : term431 = term432.
Proof. exact (@lem5333829 (NUMERAL 0) term157). Qed.
Lemma lem5333831 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333832 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333833 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333832 h1) (fun h1 : term432 = True => @lem5333831)). Qed.
Lemma lem5333834 : term432 = True.
Proof. exact (EQ_MP (@lem5333833) (@lem5333831)). Qed.
Lemma lem5333835 : term431 = True.
Proof. exact (TRANS (@lem5333830) (@lem5333834)). Qed.
Lemma lem5333836 : True = term431.
Proof. exact (SYM (@lem5333835)). Qed.
Lemma lem5333837 : term431.
Proof. exact (EQ_MP (@lem5333836) (@lem0)). Qed.
Lemma lem5333838 : term694.
Proof. exact (@lem5333827 (@lem5333837)). Qed.
Lemma lem5333840 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333841 : term431 = term432.
Proof. exact (@lem5333840 (NUMERAL 0) term157). Qed.
Lemma lem5333842 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333843 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333844 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333843 h1) (fun h1 : term432 = True => @lem5333842)). Qed.
Lemma lem5333845 : term432 = True.
Proof. exact (EQ_MP (@lem5333844) (@lem5333842)). Qed.
Lemma lem5333846 : term431 = True.
Proof. exact (TRANS (@lem5333841) (@lem5333845)). Qed.
Lemma lem5333847 : True = term431.
Proof. exact (SYM (@lem5333846)). Qed.
Lemma lem5333848 : term431.
Proof. exact (EQ_MP (@lem5333847) (@lem0)). Qed.
Lemma lem5333849 : term695.
Proof. exact (@lem5333838 (@lem5333848)). Qed.
Lemma lem5333851 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333852 : term431 = term432.
Proof. exact (@lem5333851 (NUMERAL 0) term157). Qed.
Lemma lem5333853 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333854 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333855 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333854 h1) (fun h1 : term432 = True => @lem5333853)). Qed.
Lemma lem5333856 : term432 = True.
Proof. exact (EQ_MP (@lem5333855) (@lem5333853)). Qed.
Lemma lem5333857 : term431 = True.
Proof. exact (TRANS (@lem5333852) (@lem5333856)). Qed.
Lemma lem5333858 : True = term431.
Proof. exact (SYM (@lem5333857)). Qed.
Lemma lem5333859 : term431.
Proof. exact (EQ_MP (@lem5333858) (@lem0)). Qed.
Lemma lem5333860 : term696.
Proof. exact (@lem5333849 (@lem5333859)). Qed.
Lemma lem5333862 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333863 : term364 = term365.
Proof. exact (@lem5333862 term157 term157). Qed.
Lemma lem5333864 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333865 : term367 = term157.
Proof. exact (EQ_MP (@lem5333864) (@lem940073)). Qed.
Lemma lem5333866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333867 : term365 = term305.
Proof. exact (MK_COMB (@lem5333866) (@lem5333865)). Qed.
Lemma lem5333868 : term364 = term305.
Proof. exact (TRANS (@lem5333863) (@lem5333867)). Qed.
Lemma lem5333870 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333871 : term398 = term403.
Proof. exact (@lem5333870 term157 term157). Qed.
Lemma lem5333872 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333873 : term367 = term157.
Proof. exact (EQ_MP (@lem5333872) (@lem940073)). Qed.
Lemma lem5333874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333875 : term365 = term305.
Proof. exact (MK_COMB (@lem5333874) (@lem5333873)). Qed.
Lemma lem5333876 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333877 : term403 = term355.
Proof. exact (MK_COMB (@lem5333876) (@lem5333875)). Qed.
Lemma lem5333878 : term398 = term355.
Proof. exact (TRANS (@lem5333871) (@lem5333877)). Qed.
Lemma lem5333879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333880 : term697 = term689.
Proof. exact (MK_COMB (@lem5333879) (@lem5333878)). Qed.
Lemma lem5333881 : term698 = term691.
Proof. exact (MK_COMB (@lem5333880) (@lem5333868)). Qed.
Lemma lem5333883 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5333884 : term691 = term293.
Proof. exact (@lem5333883 term157). Qed.
Lemma lem5333885 : term698 = term293.
Proof. exact (TRANS (@lem5333881) (@lem5333884)). Qed.
Lemma lem5333886 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333887 : term700 = term441.
Proof. exact (MK_COMB (@lem5333886) (@lem5333885)). Qed.
Lemma lem5333888 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5333889 : term701 = term443.
Proof. exact (MK_COMB (@lem5333887) (@lem5333888)). Qed.
Lemma lem5333891 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333892 : term443 = term293.
Proof. exact (@lem5333891 term157). Qed.
Lemma lem5333893 : term701 = term293.
Proof. exact (TRANS (@lem5333889) (@lem5333892)). Qed.
Lemma lem5333895 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333896 : term364 = term365.
Proof. exact (@lem5333895 term157 term157). Qed.
Lemma lem5333897 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333898 : term367 = term157.
Proof. exact (EQ_MP (@lem5333897) (@lem940073)). Qed.
Lemma lem5333899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333900 : term365 = term305.
Proof. exact (MK_COMB (@lem5333899) (@lem5333898)). Qed.
Lemma lem5333901 : term364 = term305.
Proof. exact (TRANS (@lem5333896) (@lem5333900)). Qed.
Lemma lem5333902 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5333903 : term445 = term443.
Proof. exact (MK_COMB (@lem5333902) (@lem5333901)). Qed.
Lemma lem5333905 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5333906 : term443 = term293.
Proof. exact (@lem5333905 term157). Qed.
Lemma lem5333907 : term445 = term293.
Proof. exact (TRANS (@lem5333903) (@lem5333906)). Qed.
Lemma lem5333908 : term293 = term445.
Proof. exact (SYM (@lem5333907)). Qed.
Lemma lem5333909 : term701 = term445.
Proof. exact (TRANS (@lem5333893) (@lem5333908)). Qed.
Lemma lem5333910 : term692 = term352.
Proof. exact (@lem5333860 (@lem5333909)). Qed.
Lemma lem5333911 : term691 = term352.
Proof. exact (TRANS (@lem5333826) (@lem5333910)). Qed.
Lemma lem5333913 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5333914 : term352 = term293.
Proof. exact (@lem5333913 term293). Qed.
Lemma lem5333915 : term691 = term293.
Proof. exact (TRANS (@lem5333911) (@lem5333914)). Qed.
Lemma lem5333916 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333917 : term702 = term441.
Proof. exact (MK_COMB (@lem5333916) (@lem5333915)). Qed.
Lemma lem5333918 (_69705 : int) : (real_of_int _69705) = (real_of_int _69705).
Proof. exact (eq_refl (real_of_int _69705)). Qed.
Lemma lem5333919 (_69705 : int) : (term688 _69705) = (term703 _69705).
Proof. exact (MK_COMB (@lem5333917) (@lem5333918 _69705)). Qed.
Lemma lem5333920 (_69705 : int) : (term687 _69705) = (term703 _69705).
Proof. exact (TRANS (@lem5333817 _69705) (@lem5333919 _69705)). Qed.
Lemma lem5333921 (_69705 : int) : (term703 _69705) = term293.
Proof. exact (@lem1982719 (real_of_int _69705)). Qed.
Lemma lem5333922 (_69705 : int) : (term687 _69705) = term293.
Proof. exact (TRANS (@lem5333920 _69705) (@lem5333921 _69705)). Qed.
Lemma lem5333923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333924 (_69705 : int) : (term704 _69705) = term705.
Proof. exact (MK_COMB (@lem5333923) (@lem5333922 _69705)). Qed.
Lemma lem5333925 (_69707 : int) : (term741 _69707) = (term707 _69707).
Proof. exact (@lem1982759 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5333926 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5333928 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5333929 : term305 = term397.
Proof. exact (@lem5333928 term157). Qed.
Lemma lem5333931 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5333932 : term355 = term356.
Proof. exact (@lem5333931 term157). Qed.
Lemma lem5333933 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333934 : term689 = term690.
Proof. exact (MK_COMB (@lem5333933) (@lem5333932)). Qed.
Lemma lem5333935 : term691 = term692.
Proof. exact (MK_COMB (@lem5333934) (@lem5333929)). Qed.
Lemma lem5333936 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5333938 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333939 : term431 = term432.
Proof. exact (@lem5333938 (NUMERAL 0) term157). Qed.
Lemma lem5333940 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333941 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333942 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333941 h1) (fun h1 : term432 = True => @lem5333940)). Qed.
Lemma lem5333943 : term432 = True.
Proof. exact (EQ_MP (@lem5333942) (@lem5333940)). Qed.
Lemma lem5333944 : term431 = True.
Proof. exact (TRANS (@lem5333939) (@lem5333943)). Qed.
Lemma lem5333945 : True = term431.
Proof. exact (SYM (@lem5333944)). Qed.
Lemma lem5333946 : term431.
Proof. exact (EQ_MP (@lem5333945) (@lem0)). Qed.
Lemma lem5333947 : term694.
Proof. exact (@lem5333936 (@lem5333946)). Qed.
Lemma lem5333949 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333950 : term431 = term432.
Proof. exact (@lem5333949 (NUMERAL 0) term157). Qed.
Lemma lem5333951 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333952 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333953 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333952 h1) (fun h1 : term432 = True => @lem5333951)). Qed.
Lemma lem5333954 : term432 = True.
Proof. exact (EQ_MP (@lem5333953) (@lem5333951)). Qed.
Lemma lem5333955 : term431 = True.
Proof. exact (TRANS (@lem5333950) (@lem5333954)). Qed.
Lemma lem5333956 : True = term431.
Proof. exact (SYM (@lem5333955)). Qed.
Lemma lem5333957 : term431.
Proof. exact (EQ_MP (@lem5333956) (@lem0)). Qed.
Lemma lem5333958 : term695.
Proof. exact (@lem5333947 (@lem5333957)). Qed.
Lemma lem5333960 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5333961 : term431 = term432.
Proof. exact (@lem5333960 (NUMERAL 0) term157). Qed.
Lemma lem5333962 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5333963 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5333964 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5333963 h1) (fun h1 : term432 = True => @lem5333962)). Qed.
Lemma lem5333965 : term432 = True.
Proof. exact (EQ_MP (@lem5333964) (@lem5333962)). Qed.
Lemma lem5333966 : term431 = True.
Proof. exact (TRANS (@lem5333961) (@lem5333965)). Qed.
Lemma lem5333967 : True = term431.
Proof. exact (SYM (@lem5333966)). Qed.
Lemma lem5333968 : term431.
Proof. exact (EQ_MP (@lem5333967) (@lem0)). Qed.
Lemma lem5333969 : term696.
Proof. exact (@lem5333958 (@lem5333968)). Qed.
Lemma lem5333971 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5333972 : term364 = term365.
Proof. exact (@lem5333971 term157 term157). Qed.
Lemma lem5333973 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333974 : term367 = term157.
Proof. exact (EQ_MP (@lem5333973) (@lem940073)). Qed.
Lemma lem5333975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333976 : term365 = term305.
Proof. exact (MK_COMB (@lem5333975) (@lem5333974)). Qed.
Lemma lem5333977 : term364 = term305.
Proof. exact (TRANS (@lem5333972) (@lem5333976)). Qed.
Lemma lem5333979 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5333980 : term398 = term403.
Proof. exact (@lem5333979 term157 term157). Qed.
Lemma lem5333981 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5333982 : term367 = term157.
Proof. exact (EQ_MP (@lem5333981) (@lem940073)). Qed.
Lemma lem5333983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5333984 : term365 = term305.
Proof. exact (MK_COMB (@lem5333983) (@lem5333982)). Qed.
Lemma lem5333985 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5333986 : term403 = term355.
Proof. exact (MK_COMB (@lem5333985) (@lem5333984)). Qed.
Lemma lem5333987 : term398 = term355.
Proof. exact (TRANS (@lem5333980) (@lem5333986)). Qed.
Lemma lem5333988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5333989 : term697 = term689.
Proof. exact (MK_COMB (@lem5333988) (@lem5333987)). Qed.
Lemma lem5333990 : term698 = term691.
Proof. exact (MK_COMB (@lem5333989) (@lem5333977)). Qed.
Lemma lem5333992 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5333993 : term691 = term293.
Proof. exact (@lem5333992 term157). Qed.
Lemma lem5333994 : term698 = term293.
Proof. exact (TRANS (@lem5333990) (@lem5333993)). Qed.
Lemma lem5333995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5333996 : term700 = term441.
Proof. exact (MK_COMB (@lem5333995) (@lem5333994)). Qed.
Lemma lem5333997 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5333998 : term701 = term443.
Proof. exact (MK_COMB (@lem5333996) (@lem5333997)). Qed.
Lemma lem5334000 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334001 : term443 = term293.
Proof. exact (@lem5334000 term157). Qed.
Lemma lem5334002 : term701 = term293.
Proof. exact (TRANS (@lem5333998) (@lem5334001)). Qed.
Lemma lem5334004 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334005 : term364 = term365.
Proof. exact (@lem5334004 term157 term157). Qed.
Lemma lem5334006 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334007 : term367 = term157.
Proof. exact (EQ_MP (@lem5334006) (@lem940073)). Qed.
Lemma lem5334008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334009 : term365 = term305.
Proof. exact (MK_COMB (@lem5334008) (@lem5334007)). Qed.
Lemma lem5334010 : term364 = term305.
Proof. exact (TRANS (@lem5334005) (@lem5334009)). Qed.
Lemma lem5334011 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5334012 : term445 = term443.
Proof. exact (MK_COMB (@lem5334011) (@lem5334010)). Qed.
Lemma lem5334014 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334015 : term443 = term293.
Proof. exact (@lem5334014 term157). Qed.
Lemma lem5334016 : term445 = term293.
Proof. exact (TRANS (@lem5334012) (@lem5334015)). Qed.
Lemma lem5334017 : term293 = term445.
Proof. exact (SYM (@lem5334016)). Qed.
Lemma lem5334018 : term701 = term445.
Proof. exact (TRANS (@lem5334002) (@lem5334017)). Qed.
Lemma lem5334019 : term692 = term352.
Proof. exact (@lem5333969 (@lem5334018)). Qed.
Lemma lem5334020 : term691 = term352.
Proof. exact (TRANS (@lem5333935) (@lem5334019)). Qed.
Lemma lem5334022 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5334023 : term352 = term293.
Proof. exact (@lem5334022 term293). Qed.
Lemma lem5334024 : term691 = term293.
Proof. exact (TRANS (@lem5334020) (@lem5334023)). Qed.
Lemma lem5334025 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334026 : term702 = term441.
Proof. exact (MK_COMB (@lem5334025) (@lem5334024)). Qed.
Lemma lem5334027 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5334028 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5334026) (@lem5334027 _69707)). Qed.
Lemma lem5334029 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5333926 _69707) (@lem5334028 _69707)). Qed.
Lemma lem5334030 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5334031 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5334029 _69707) (@lem5334030 _69707)). Qed.
Lemma lem5334032 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334033 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5334032) (@lem5334031 _69707)). Qed.
Lemma lem5334034 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5334035 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5334033 _69707) (@lem5334034)). Qed.
Lemma lem5334036 (_69707 : int) : (term741 _69707) = term710.
Proof. exact (TRANS (@lem5333925 _69707) (@lem5334035 _69707)). Qed.
Lemma lem5334037 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5334038 (_69707 : int) : (term741 _69707) = term355.
Proof. exact (TRANS (@lem5334036 _69707) (@lem5334037)). Qed.
Lemma lem5334039 (_69705 : int) (_69707 : int) : (term739 _69705 _69707) = term710.
Proof. exact (MK_COMB (@lem5333924 _69705) (@lem5334038 _69707)). Qed.
Lemma lem5334040 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = term710.
Proof. exact (TRANS (@lem5333816 _69705 _69707) (@lem5334039 _69705 _69707)). Qed.
Lemma lem5334041 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5334042 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = term355.
Proof. exact (TRANS (@lem5334040 _69705 _69707) (@lem5334041)). Qed.
Lemma lem5334043 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334044 (_69705 : int) (_69707 : int) : (term742 _69705 _69707) = term712.
Proof. exact (MK_COMB (@lem5334043) (@lem5334042 _69705 _69707)). Qed.
Lemma lem5334045 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334046 (_69705 : int) (_69707 : int) : (term737 _69705 _69707) = term713.
Proof. exact (MK_COMB (@lem5334044 _69705 _69707) (@lem5334045)). Qed.
Lemma lem5334047 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5334046 _69705 _69707) (@lem5333815 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5334049 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5334050 : term713 = term714.
Proof. exact (@lem5334049 term293 term355). Qed.
Lemma lem5334052 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334053 : term355 = term356.
Proof. exact (@lem5334052 term157). Qed.
Lemma lem5334055 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334056 : term293 = term352.
Proof. exact (@lem5334055 (NUMERAL 0)). Qed.
Lemma lem5334057 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5334058 : term295 = term715.
Proof. exact (MK_COMB (@lem5334057) (@lem5334056)). Qed.
Lemma lem5334059 : term714 = term716.
Proof. exact (MK_COMB (@lem5334058) (@lem5334053)). Qed.
Lemma lem5334060 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5334062 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334063 : term431 = term432.
Proof. exact (@lem5334062 (NUMERAL 0) term157). Qed.
Lemma lem5334064 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334065 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334066 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334065 h1) (fun h1 : term432 = True => @lem5334064)). Qed.
Lemma lem5334067 : term432 = True.
Proof. exact (EQ_MP (@lem5334066) (@lem5334064)). Qed.
Lemma lem5334068 : term431 = True.
Proof. exact (TRANS (@lem5334063) (@lem5334067)). Qed.
Lemma lem5334069 : True = term431.
Proof. exact (SYM (@lem5334068)). Qed.
Lemma lem5334070 : term431.
Proof. exact (EQ_MP (@lem5334069) (@lem0)). Qed.
Lemma lem5334071 : term718.
Proof. exact (@lem5334060 (@lem5334070)). Qed.
Lemma lem5334073 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334074 : term431 = term432.
Proof. exact (@lem5334073 (NUMERAL 0) term157). Qed.
Lemma lem5334075 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334076 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334077 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334076 h1) (fun h1 : term432 = True => @lem5334075)). Qed.
Lemma lem5334078 : term432 = True.
Proof. exact (EQ_MP (@lem5334077) (@lem5334075)). Qed.
Lemma lem5334079 : term431 = True.
Proof. exact (TRANS (@lem5334074) (@lem5334078)). Qed.
Lemma lem5334080 : True = term431.
Proof. exact (SYM (@lem5334079)). Qed.
Lemma lem5334081 : term431.
Proof. exact (EQ_MP (@lem5334080) (@lem0)). Qed.
Lemma lem5334082 : term716 = term719.
Proof. exact (@lem5334071 (@lem5334081)). Qed.
Lemma lem5334084 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334085 : term398 = term403.
Proof. exact (@lem5334084 term157 term157). Qed.
Lemma lem5334086 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334087 : term367 = term157.
Proof. exact (EQ_MP (@lem5334086) (@lem940073)). Qed.
Lemma lem5334088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334089 : term365 = term305.
Proof. exact (MK_COMB (@lem5334088) (@lem5334087)). Qed.
Lemma lem5334090 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5334091 : term403 = term355.
Proof. exact (MK_COMB (@lem5334090) (@lem5334089)). Qed.
Lemma lem5334092 : term398 = term355.
Proof. exact (TRANS (@lem5334085) (@lem5334091)). Qed.
Lemma lem5334094 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334095 : term443 = term293.
Proof. exact (@lem5334094 term157). Qed.
Lemma lem5334096 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5334097 : term720 = term295.
Proof. exact (MK_COMB (@lem5334096) (@lem5334095)). Qed.
Lemma lem5334098 : term719 = term714.
Proof. exact (MK_COMB (@lem5334097) (@lem5334092)). Qed.
Lemma lem5334100 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5334101 : term714 = term723.
Proof. exact (@lem5334100 (NUMERAL 0) term157). Qed.
Lemma lem5334102 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334103 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5334104 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334103 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5334102)). Qed.
Lemma lem5334105 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5334104) (@lem5334102)). Qed.
Lemma lem5334106 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5334107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5334108 : term724 = (and True).
Proof. exact (MK_COMB (@lem5334107) (@lem5334106)). Qed.
Lemma lem5334109 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5334108) (@lem5334105)). Qed.
Lemma lem5334111 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5334112 : term723 = False.
Proof. exact (TRANS (@lem5334109) (@lem5334111)). Qed.
Lemma lem5334113 : term714 = False.
Proof. exact (TRANS (@lem5334101) (@lem5334112)). Qed.
Lemma lem5334114 : term719 = False.
Proof. exact (TRANS (@lem5334098) (@lem5334113)). Qed.
Lemma lem5334115 : term716 = False.
Proof. exact (TRANS (@lem5334082) (@lem5334114)). Qed.
Lemma lem5334116 : term714 = False.
Proof. exact (TRANS (@lem5334059) (@lem5334115)). Qed.
Lemma lem5334117 : term713 = False.
Proof. exact (TRANS (@lem5334050) (@lem5334116)). Qed.
Lemma lem5334118 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term744 _69706 _69704 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5334117) (@lem5334047 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5334119 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term648 _69706 _69704 _69705 _69707) : False.
Proof. exact (or_elim (@lem5333168 _69706 _69704 _69705 _69707 h1) (fun h0 : term743 _69706 _69704 _69705 _69707 => @lem5333643 _69706 _69704 _69705 _69707 h0) (fun h0 : term744 _69706 _69704 _69705 _69707 => @lem5334118 _69706 _69704 _69705 _69707 h0)). Qed.
Lemma lem5334120 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term657 _69706 _69704 _69705 _69707) : False.
Proof. exact (or_elim (@lem5332215 _69706 _69704 _69705 _69707 h1) (fun h0 : term652 _69706 _69704 _69705 _69707 => @lem5333167 _69706 _69704 _69705 _69707 h0) (fun h0 : term648 _69706 _69704 _69705 _69707 => @lem5334119 _69706 _69704 _69705 _69707 h0)). Qed.
Lemma lem5334121 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term644 _69704 _69706 _69705 _69707) : term644 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5334122 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term639 _69706 _69705 _69704 _69707) : term639 _69706 _69705 _69704 _69707.
Proof. exact (h1). Qed.
Lemma lem5334123 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term745 _69705 _69706 _69704 _69707.
Proof. exact (h1). Qed.
Lemma lem5334124 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term640 _69705 _69706 _69704 _69707.
Proof. exact (proj2 (@lem5334123 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334126 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term609 _69705 _69706 _69704 _69707.
Proof. exact (proj2 (@lem5334124 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334128 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term578 _69705 _69706 _69704 _69707.
Proof. exact (proj2 (@lem5334126 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334130 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term547 _69705 _69706 _69704 _69707.
Proof. exact (proj2 (@lem5334128 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334132 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term516 _69706 _69704 _69707.
Proof. exact (proj2 (@lem5334130 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334136 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term411 _69704 _69707.
Proof. exact (proj2 (@lem5334132 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334137 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term456 _69704 _69706 _69707.
Proof. exact (proj1 (@lem5334132 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334139 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term454 _69704 _69707.
Proof. exact (proj1 (@lem5334137 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334141 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5334142 : term662 = term431.
Proof. exact (@lem5334141 term293 term305). Qed.
Lemma lem5334144 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334145 : term305 = term397.
Proof. exact (@lem5334144 term157). Qed.
Lemma lem5334147 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334148 : term293 = term352.
Proof. exact (@lem5334147 (NUMERAL 0)). Qed.
Lemma lem5334149 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334150 : term663 = term664.
Proof. exact (MK_COMB (@lem5334149) (@lem5334148)). Qed.
Lemma lem5334151 : term431 = term665.
Proof. exact (MK_COMB (@lem5334150) (@lem5334145)). Qed.
Lemma lem5334152 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5334154 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334155 : term431 = term432.
Proof. exact (@lem5334154 (NUMERAL 0) term157). Qed.
Lemma lem5334156 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334157 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334158 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334157 h1) (fun h1 : term432 = True => @lem5334156)). Qed.
Lemma lem5334159 : term432 = True.
Proof. exact (EQ_MP (@lem5334158) (@lem5334156)). Qed.
Lemma lem5334160 : term431 = True.
Proof. exact (TRANS (@lem5334155) (@lem5334159)). Qed.
Lemma lem5334161 : True = term431.
Proof. exact (SYM (@lem5334160)). Qed.
Lemma lem5334162 : term431.
Proof. exact (EQ_MP (@lem5334161) (@lem0)). Qed.
Lemma lem5334163 : term667.
Proof. exact (@lem5334152 (@lem5334162)). Qed.
Lemma lem5334165 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334166 : term431 = term432.
Proof. exact (@lem5334165 (NUMERAL 0) term157). Qed.
Lemma lem5334167 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334168 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334169 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334168 h1) (fun h1 : term432 = True => @lem5334167)). Qed.
Lemma lem5334170 : term432 = True.
Proof. exact (EQ_MP (@lem5334169) (@lem5334167)). Qed.
Lemma lem5334171 : term431 = True.
Proof. exact (TRANS (@lem5334166) (@lem5334170)). Qed.
Lemma lem5334172 : True = term431.
Proof. exact (SYM (@lem5334171)). Qed.
Lemma lem5334173 : term431.
Proof. exact (EQ_MP (@lem5334172) (@lem0)). Qed.
Lemma lem5334174 : term665 = term668.
Proof. exact (@lem5334163 (@lem5334173)). Qed.
Lemma lem5334176 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334177 : term364 = term365.
Proof. exact (@lem5334176 term157 term157). Qed.
Lemma lem5334178 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334179 : term367 = term157.
Proof. exact (EQ_MP (@lem5334178) (@lem940073)). Qed.
Lemma lem5334180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334181 : term365 = term305.
Proof. exact (MK_COMB (@lem5334180) (@lem5334179)). Qed.
Lemma lem5334182 : term364 = term305.
Proof. exact (TRANS (@lem5334177) (@lem5334181)). Qed.
Lemma lem5334184 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334185 : term443 = term293.
Proof. exact (@lem5334184 term157). Qed.
Lemma lem5334186 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334187 : term669 = term663.
Proof. exact (MK_COMB (@lem5334186) (@lem5334185)). Qed.
Lemma lem5334188 : term668 = term431.
Proof. exact (MK_COMB (@lem5334187) (@lem5334182)). Qed.
Lemma lem5334190 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334191 : term431 = term432.
Proof. exact (@lem5334190 (NUMERAL 0) term157). Qed.
Lemma lem5334192 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334193 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334194 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334193 h1) (fun h1 : term432 = True => @lem5334192)). Qed.
Lemma lem5334195 : term432 = True.
Proof. exact (EQ_MP (@lem5334194) (@lem5334192)). Qed.
Lemma lem5334196 : term431 = True.
Proof. exact (TRANS (@lem5334191) (@lem5334195)). Qed.
Lemma lem5334197 : term668 = True.
Proof. exact (TRANS (@lem5334188) (@lem5334196)). Qed.
Lemma lem5334198 : term665 = True.
Proof. exact (TRANS (@lem5334174) (@lem5334197)). Qed.
Lemma lem5334199 : term431 = True.
Proof. exact (TRANS (@lem5334151) (@lem5334198)). Qed.
Lemma lem5334200 : term662 = True.
Proof. exact (TRANS (@lem5334142) (@lem5334199)). Qed.
Lemma lem5334201 : True = term662.
Proof. exact (SYM (@lem5334200)). Qed.
Lemma lem5334202 : term662.
Proof. exact (EQ_MP (@lem5334201) (@lem0)). Qed.
Lemma lem5334203 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term670 _69704 _69707.
Proof. exact (conj (@lem5334202) (@lem5334136 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334205 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5334206 (_69704 : int) (_69707 : int) : term672 _69704 _69707.
Proof. exact (@lem5334205 term305 (term408 _69704 _69707)). Qed.
Lemma lem5334207 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term673 _69704 _69707.
Proof. exact (@lem5334206 _69704 _69707 (@lem5334203 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334208 (_69704 : int) (_69707 : int) : (term674 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (@lem1982733 (term408 _69704 _69707)). Qed.
Lemma lem5334209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334210 (_69704 : int) (_69707 : int) : (term675 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5334209) (@lem5334208 _69704 _69707)). Qed.
Lemma lem5334211 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334212 (_69704 : int) (_69707 : int) : (term673 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5334210 _69704 _69707) (@lem5334211)). Qed.
Lemma lem5334213 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term411 _69704 _69707.
Proof. exact (EQ_MP (@lem5334212 _69704 _69707) (@lem5334207 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334215 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5334216 : term662 = term431.
Proof. exact (@lem5334215 term293 term305). Qed.
Lemma lem5334218 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334219 : term305 = term397.
Proof. exact (@lem5334218 term157). Qed.
Lemma lem5334221 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334222 : term293 = term352.
Proof. exact (@lem5334221 (NUMERAL 0)). Qed.
Lemma lem5334223 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334224 : term663 = term664.
Proof. exact (MK_COMB (@lem5334223) (@lem5334222)). Qed.
Lemma lem5334225 : term431 = term665.
Proof. exact (MK_COMB (@lem5334224) (@lem5334219)). Qed.
Lemma lem5334226 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5334228 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334229 : term431 = term432.
Proof. exact (@lem5334228 (NUMERAL 0) term157). Qed.
Lemma lem5334230 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334231 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334232 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334231 h1) (fun h1 : term432 = True => @lem5334230)). Qed.
Lemma lem5334233 : term432 = True.
Proof. exact (EQ_MP (@lem5334232) (@lem5334230)). Qed.
Lemma lem5334234 : term431 = True.
Proof. exact (TRANS (@lem5334229) (@lem5334233)). Qed.
Lemma lem5334235 : True = term431.
Proof. exact (SYM (@lem5334234)). Qed.
Lemma lem5334236 : term431.
Proof. exact (EQ_MP (@lem5334235) (@lem0)). Qed.
Lemma lem5334237 : term667.
Proof. exact (@lem5334226 (@lem5334236)). Qed.
Lemma lem5334239 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334240 : term431 = term432.
Proof. exact (@lem5334239 (NUMERAL 0) term157). Qed.
Lemma lem5334241 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334242 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334243 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334242 h1) (fun h1 : term432 = True => @lem5334241)). Qed.
Lemma lem5334244 : term432 = True.
Proof. exact (EQ_MP (@lem5334243) (@lem5334241)). Qed.
Lemma lem5334245 : term431 = True.
Proof. exact (TRANS (@lem5334240) (@lem5334244)). Qed.
Lemma lem5334246 : True = term431.
Proof. exact (SYM (@lem5334245)). Qed.
Lemma lem5334247 : term431.
Proof. exact (EQ_MP (@lem5334246) (@lem0)). Qed.
Lemma lem5334248 : term665 = term668.
Proof. exact (@lem5334237 (@lem5334247)). Qed.
Lemma lem5334250 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334251 : term364 = term365.
Proof. exact (@lem5334250 term157 term157). Qed.
Lemma lem5334252 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334253 : term367 = term157.
Proof. exact (EQ_MP (@lem5334252) (@lem940073)). Qed.
Lemma lem5334254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334255 : term365 = term305.
Proof. exact (MK_COMB (@lem5334254) (@lem5334253)). Qed.
Lemma lem5334256 : term364 = term305.
Proof. exact (TRANS (@lem5334251) (@lem5334255)). Qed.
Lemma lem5334258 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334259 : term443 = term293.
Proof. exact (@lem5334258 term157). Qed.
Lemma lem5334260 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334261 : term669 = term663.
Proof. exact (MK_COMB (@lem5334260) (@lem5334259)). Qed.
Lemma lem5334262 : term668 = term431.
Proof. exact (MK_COMB (@lem5334261) (@lem5334256)). Qed.
Lemma lem5334264 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334265 : term431 = term432.
Proof. exact (@lem5334264 (NUMERAL 0) term157). Qed.
Lemma lem5334266 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334267 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334268 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334267 h1) (fun h1 : term432 = True => @lem5334266)). Qed.
Lemma lem5334269 : term432 = True.
Proof. exact (EQ_MP (@lem5334268) (@lem5334266)). Qed.
Lemma lem5334270 : term431 = True.
Proof. exact (TRANS (@lem5334265) (@lem5334269)). Qed.
Lemma lem5334271 : term668 = True.
Proof. exact (TRANS (@lem5334262) (@lem5334270)). Qed.
Lemma lem5334272 : term665 = True.
Proof. exact (TRANS (@lem5334248) (@lem5334271)). Qed.
Lemma lem5334273 : term431 = True.
Proof. exact (TRANS (@lem5334225) (@lem5334272)). Qed.
Lemma lem5334274 : term662 = True.
Proof. exact (TRANS (@lem5334216) (@lem5334273)). Qed.
Lemma lem5334275 : True = term662.
Proof. exact (SYM (@lem5334274)). Qed.
Lemma lem5334276 : term662.
Proof. exact (EQ_MP (@lem5334275) (@lem0)). Qed.
Lemma lem5334277 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term676 _69704 _69707.
Proof. exact (conj (@lem5334276) (@lem5334139 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334279 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5334280 (_69704 : int) (_69707 : int) : term677 _69704 _69707.
Proof. exact (@lem5334279 term305 (term452 _69704 _69707)). Qed.
Lemma lem5334281 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term678 _69704 _69707.
Proof. exact (@lem5334280 _69704 _69707 (@lem5334277 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334282 (_69704 : int) (_69707 : int) : (term679 _69704 _69707) = (term452 _69704 _69707).
Proof. exact (@lem1982733 (term452 _69704 _69707)). Qed.
Lemma lem5334283 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334284 (_69704 : int) (_69707 : int) : (term680 _69704 _69707) = (term453 _69704 _69707).
Proof. exact (MK_COMB (@lem5334283) (@lem5334282 _69704 _69707)). Qed.
Lemma lem5334285 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334286 (_69704 : int) (_69707 : int) : (term678 _69704 _69707) = (term454 _69704 _69707).
Proof. exact (MK_COMB (@lem5334284 _69704 _69707) (@lem5334285)). Qed.
Lemma lem5334287 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term454 _69704 _69707.
Proof. exact (EQ_MP (@lem5334286 _69704 _69707) (@lem5334281 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334288 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term681 _69704 _69707.
Proof. exact (conj (@lem5334287 _69705 _69706 _69704 _69707 h1) (@lem5334213 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334290 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5334291 (_69704 : int) (_69707 : int) : term683 _69704 _69707.
Proof. exact (@lem5334290 (term452 _69704 _69707) (term408 _69704 _69707)). Qed.
Lemma lem5334292 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term684 _69704 _69707.
Proof. exact (@lem5334291 _69704 _69707 (@lem5334288 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334293 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = (term686 _69704 _69707).
Proof. exact (@lem1982753 (term380 _69704) (real_of_int _69704) (real_of_int _69707) (term407 _69707)). Qed.
Lemma lem5334294 (_69704 : int) : (term687 _69704) = (term688 _69704).
Proof. exact (@lem1982713 term355 (real_of_int _69704)). Qed.
Lemma lem5334296 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334297 : term305 = term397.
Proof. exact (@lem5334296 term157). Qed.
Lemma lem5334299 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334300 : term355 = term356.
Proof. exact (@lem5334299 term157). Qed.
Lemma lem5334301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334302 : term689 = term690.
Proof. exact (MK_COMB (@lem5334301) (@lem5334300)). Qed.
Lemma lem5334303 : term691 = term692.
Proof. exact (MK_COMB (@lem5334302) (@lem5334297)). Qed.
Lemma lem5334304 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5334306 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334307 : term431 = term432.
Proof. exact (@lem5334306 (NUMERAL 0) term157). Qed.
Lemma lem5334308 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334309 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334310 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334309 h1) (fun h1 : term432 = True => @lem5334308)). Qed.
Lemma lem5334311 : term432 = True.
Proof. exact (EQ_MP (@lem5334310) (@lem5334308)). Qed.
Lemma lem5334312 : term431 = True.
Proof. exact (TRANS (@lem5334307) (@lem5334311)). Qed.
Lemma lem5334313 : True = term431.
Proof. exact (SYM (@lem5334312)). Qed.
Lemma lem5334314 : term431.
Proof. exact (EQ_MP (@lem5334313) (@lem0)). Qed.
Lemma lem5334315 : term694.
Proof. exact (@lem5334304 (@lem5334314)). Qed.
Lemma lem5334317 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334318 : term431 = term432.
Proof. exact (@lem5334317 (NUMERAL 0) term157). Qed.
Lemma lem5334319 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334320 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334321 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334320 h1) (fun h1 : term432 = True => @lem5334319)). Qed.
Lemma lem5334322 : term432 = True.
Proof. exact (EQ_MP (@lem5334321) (@lem5334319)). Qed.
Lemma lem5334323 : term431 = True.
Proof. exact (TRANS (@lem5334318) (@lem5334322)). Qed.
Lemma lem5334324 : True = term431.
Proof. exact (SYM (@lem5334323)). Qed.
Lemma lem5334325 : term431.
Proof. exact (EQ_MP (@lem5334324) (@lem0)). Qed.
Lemma lem5334326 : term695.
Proof. exact (@lem5334315 (@lem5334325)). Qed.
Lemma lem5334328 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334329 : term431 = term432.
Proof. exact (@lem5334328 (NUMERAL 0) term157). Qed.
Lemma lem5334330 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334331 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334332 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334331 h1) (fun h1 : term432 = True => @lem5334330)). Qed.
Lemma lem5334333 : term432 = True.
Proof. exact (EQ_MP (@lem5334332) (@lem5334330)). Qed.
Lemma lem5334334 : term431 = True.
Proof. exact (TRANS (@lem5334329) (@lem5334333)). Qed.
Lemma lem5334335 : True = term431.
Proof. exact (SYM (@lem5334334)). Qed.
Lemma lem5334336 : term431.
Proof. exact (EQ_MP (@lem5334335) (@lem0)). Qed.
Lemma lem5334337 : term696.
Proof. exact (@lem5334326 (@lem5334336)). Qed.
Lemma lem5334339 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334340 : term364 = term365.
Proof. exact (@lem5334339 term157 term157). Qed.
Lemma lem5334341 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334342 : term367 = term157.
Proof. exact (EQ_MP (@lem5334341) (@lem940073)). Qed.
Lemma lem5334343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334344 : term365 = term305.
Proof. exact (MK_COMB (@lem5334343) (@lem5334342)). Qed.
Lemma lem5334345 : term364 = term305.
Proof. exact (TRANS (@lem5334340) (@lem5334344)). Qed.
Lemma lem5334347 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334348 : term398 = term403.
Proof. exact (@lem5334347 term157 term157). Qed.
Lemma lem5334349 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334350 : term367 = term157.
Proof. exact (EQ_MP (@lem5334349) (@lem940073)). Qed.
Lemma lem5334351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334352 : term365 = term305.
Proof. exact (MK_COMB (@lem5334351) (@lem5334350)). Qed.
Lemma lem5334353 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5334354 : term403 = term355.
Proof. exact (MK_COMB (@lem5334353) (@lem5334352)). Qed.
Lemma lem5334355 : term398 = term355.
Proof. exact (TRANS (@lem5334348) (@lem5334354)). Qed.
Lemma lem5334356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334357 : term697 = term689.
Proof. exact (MK_COMB (@lem5334356) (@lem5334355)). Qed.
Lemma lem5334358 : term698 = term691.
Proof. exact (MK_COMB (@lem5334357) (@lem5334345)). Qed.
Lemma lem5334360 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5334361 : term691 = term293.
Proof. exact (@lem5334360 term157). Qed.
Lemma lem5334362 : term698 = term293.
Proof. exact (TRANS (@lem5334358) (@lem5334361)). Qed.
Lemma lem5334363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334364 : term700 = term441.
Proof. exact (MK_COMB (@lem5334363) (@lem5334362)). Qed.
Lemma lem5334365 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5334366 : term701 = term443.
Proof. exact (MK_COMB (@lem5334364) (@lem5334365)). Qed.
Lemma lem5334368 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334369 : term443 = term293.
Proof. exact (@lem5334368 term157). Qed.
Lemma lem5334370 : term701 = term293.
Proof. exact (TRANS (@lem5334366) (@lem5334369)). Qed.
Lemma lem5334372 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334373 : term364 = term365.
Proof. exact (@lem5334372 term157 term157). Qed.
Lemma lem5334374 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334375 : term367 = term157.
Proof. exact (EQ_MP (@lem5334374) (@lem940073)). Qed.
Lemma lem5334376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334377 : term365 = term305.
Proof. exact (MK_COMB (@lem5334376) (@lem5334375)). Qed.
Lemma lem5334378 : term364 = term305.
Proof. exact (TRANS (@lem5334373) (@lem5334377)). Qed.
Lemma lem5334379 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5334380 : term445 = term443.
Proof. exact (MK_COMB (@lem5334379) (@lem5334378)). Qed.
Lemma lem5334382 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334383 : term443 = term293.
Proof. exact (@lem5334382 term157). Qed.
Lemma lem5334384 : term445 = term293.
Proof. exact (TRANS (@lem5334380) (@lem5334383)). Qed.
Lemma lem5334385 : term293 = term445.
Proof. exact (SYM (@lem5334384)). Qed.
Lemma lem5334386 : term701 = term445.
Proof. exact (TRANS (@lem5334370) (@lem5334385)). Qed.
Lemma lem5334387 : term692 = term352.
Proof. exact (@lem5334337 (@lem5334386)). Qed.
Lemma lem5334388 : term691 = term352.
Proof. exact (TRANS (@lem5334303) (@lem5334387)). Qed.
Lemma lem5334390 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5334391 : term352 = term293.
Proof. exact (@lem5334390 term293). Qed.
Lemma lem5334392 : term691 = term293.
Proof. exact (TRANS (@lem5334388) (@lem5334391)). Qed.
Lemma lem5334393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334394 : term702 = term441.
Proof. exact (MK_COMB (@lem5334393) (@lem5334392)). Qed.
Lemma lem5334395 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5334396 (_69704 : int) : (term688 _69704) = (term703 _69704).
Proof. exact (MK_COMB (@lem5334394) (@lem5334395 _69704)). Qed.
Lemma lem5334397 (_69704 : int) : (term687 _69704) = (term703 _69704).
Proof. exact (TRANS (@lem5334294 _69704) (@lem5334396 _69704)). Qed.
Lemma lem5334398 (_69704 : int) : (term703 _69704) = term293.
Proof. exact (@lem1982719 (real_of_int _69704)). Qed.
Lemma lem5334399 (_69704 : int) : (term687 _69704) = term293.
Proof. exact (TRANS (@lem5334397 _69704) (@lem5334398 _69704)). Qed.
Lemma lem5334400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334401 (_69704 : int) : (term704 _69704) = term705.
Proof. exact (MK_COMB (@lem5334400) (@lem5334399 _69704)). Qed.
Lemma lem5334402 (_69707 : int) : (term706 _69707) = (term707 _69707).
Proof. exact (@lem1982763 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5334403 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5334405 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334406 : term305 = term397.
Proof. exact (@lem5334405 term157). Qed.
Lemma lem5334408 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334409 : term355 = term356.
Proof. exact (@lem5334408 term157). Qed.
Lemma lem5334410 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334411 : term689 = term690.
Proof. exact (MK_COMB (@lem5334410) (@lem5334409)). Qed.
Lemma lem5334412 : term691 = term692.
Proof. exact (MK_COMB (@lem5334411) (@lem5334406)). Qed.
Lemma lem5334413 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5334415 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334416 : term431 = term432.
Proof. exact (@lem5334415 (NUMERAL 0) term157). Qed.
Lemma lem5334417 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334418 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334419 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334418 h1) (fun h1 : term432 = True => @lem5334417)). Qed.
Lemma lem5334420 : term432 = True.
Proof. exact (EQ_MP (@lem5334419) (@lem5334417)). Qed.
Lemma lem5334421 : term431 = True.
Proof. exact (TRANS (@lem5334416) (@lem5334420)). Qed.
Lemma lem5334422 : True = term431.
Proof. exact (SYM (@lem5334421)). Qed.
Lemma lem5334423 : term431.
Proof. exact (EQ_MP (@lem5334422) (@lem0)). Qed.
Lemma lem5334424 : term694.
Proof. exact (@lem5334413 (@lem5334423)). Qed.
Lemma lem5334426 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334427 : term431 = term432.
Proof. exact (@lem5334426 (NUMERAL 0) term157). Qed.
Lemma lem5334428 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334429 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334430 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334429 h1) (fun h1 : term432 = True => @lem5334428)). Qed.
Lemma lem5334431 : term432 = True.
Proof. exact (EQ_MP (@lem5334430) (@lem5334428)). Qed.
Lemma lem5334432 : term431 = True.
Proof. exact (TRANS (@lem5334427) (@lem5334431)). Qed.
Lemma lem5334433 : True = term431.
Proof. exact (SYM (@lem5334432)). Qed.
Lemma lem5334434 : term431.
Proof. exact (EQ_MP (@lem5334433) (@lem0)). Qed.
Lemma lem5334435 : term695.
Proof. exact (@lem5334424 (@lem5334434)). Qed.
Lemma lem5334437 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334438 : term431 = term432.
Proof. exact (@lem5334437 (NUMERAL 0) term157). Qed.
Lemma lem5334439 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334440 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334441 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334440 h1) (fun h1 : term432 = True => @lem5334439)). Qed.
Lemma lem5334442 : term432 = True.
Proof. exact (EQ_MP (@lem5334441) (@lem5334439)). Qed.
Lemma lem5334443 : term431 = True.
Proof. exact (TRANS (@lem5334438) (@lem5334442)). Qed.
Lemma lem5334444 : True = term431.
Proof. exact (SYM (@lem5334443)). Qed.
Lemma lem5334445 : term431.
Proof. exact (EQ_MP (@lem5334444) (@lem0)). Qed.
Lemma lem5334446 : term696.
Proof. exact (@lem5334435 (@lem5334445)). Qed.
Lemma lem5334448 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334449 : term364 = term365.
Proof. exact (@lem5334448 term157 term157). Qed.
Lemma lem5334450 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334451 : term367 = term157.
Proof. exact (EQ_MP (@lem5334450) (@lem940073)). Qed.
Lemma lem5334452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334453 : term365 = term305.
Proof. exact (MK_COMB (@lem5334452) (@lem5334451)). Qed.
Lemma lem5334454 : term364 = term305.
Proof. exact (TRANS (@lem5334449) (@lem5334453)). Qed.
Lemma lem5334456 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334457 : term398 = term403.
Proof. exact (@lem5334456 term157 term157). Qed.
Lemma lem5334458 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334459 : term367 = term157.
Proof. exact (EQ_MP (@lem5334458) (@lem940073)). Qed.
Lemma lem5334460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334461 : term365 = term305.
Proof. exact (MK_COMB (@lem5334460) (@lem5334459)). Qed.
Lemma lem5334462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5334463 : term403 = term355.
Proof. exact (MK_COMB (@lem5334462) (@lem5334461)). Qed.
Lemma lem5334464 : term398 = term355.
Proof. exact (TRANS (@lem5334457) (@lem5334463)). Qed.
Lemma lem5334465 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334466 : term697 = term689.
Proof. exact (MK_COMB (@lem5334465) (@lem5334464)). Qed.
Lemma lem5334467 : term698 = term691.
Proof. exact (MK_COMB (@lem5334466) (@lem5334454)). Qed.
Lemma lem5334469 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5334470 : term691 = term293.
Proof. exact (@lem5334469 term157). Qed.
Lemma lem5334471 : term698 = term293.
Proof. exact (TRANS (@lem5334467) (@lem5334470)). Qed.
Lemma lem5334472 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334473 : term700 = term441.
Proof. exact (MK_COMB (@lem5334472) (@lem5334471)). Qed.
Lemma lem5334474 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5334475 : term701 = term443.
Proof. exact (MK_COMB (@lem5334473) (@lem5334474)). Qed.
Lemma lem5334477 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334478 : term443 = term293.
Proof. exact (@lem5334477 term157). Qed.
Lemma lem5334479 : term701 = term293.
Proof. exact (TRANS (@lem5334475) (@lem5334478)). Qed.
Lemma lem5334481 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334482 : term364 = term365.
Proof. exact (@lem5334481 term157 term157). Qed.
Lemma lem5334483 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334484 : term367 = term157.
Proof. exact (EQ_MP (@lem5334483) (@lem940073)). Qed.
Lemma lem5334485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334486 : term365 = term305.
Proof. exact (MK_COMB (@lem5334485) (@lem5334484)). Qed.
Lemma lem5334487 : term364 = term305.
Proof. exact (TRANS (@lem5334482) (@lem5334486)). Qed.
Lemma lem5334488 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5334489 : term445 = term443.
Proof. exact (MK_COMB (@lem5334488) (@lem5334487)). Qed.
Lemma lem5334491 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334492 : term443 = term293.
Proof. exact (@lem5334491 term157). Qed.
Lemma lem5334493 : term445 = term293.
Proof. exact (TRANS (@lem5334489) (@lem5334492)). Qed.
Lemma lem5334494 : term293 = term445.
Proof. exact (SYM (@lem5334493)). Qed.
Lemma lem5334495 : term701 = term445.
Proof. exact (TRANS (@lem5334479) (@lem5334494)). Qed.
Lemma lem5334496 : term692 = term352.
Proof. exact (@lem5334446 (@lem5334495)). Qed.
Lemma lem5334497 : term691 = term352.
Proof. exact (TRANS (@lem5334412) (@lem5334496)). Qed.
Lemma lem5334499 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5334500 : term352 = term293.
Proof. exact (@lem5334499 term293). Qed.
Lemma lem5334501 : term691 = term293.
Proof. exact (TRANS (@lem5334497) (@lem5334500)). Qed.
Lemma lem5334502 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334503 : term702 = term441.
Proof. exact (MK_COMB (@lem5334502) (@lem5334501)). Qed.
Lemma lem5334504 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5334505 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5334503) (@lem5334504 _69707)). Qed.
Lemma lem5334506 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5334403 _69707) (@lem5334505 _69707)). Qed.
Lemma lem5334507 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5334508 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5334506 _69707) (@lem5334507 _69707)). Qed.
Lemma lem5334509 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334510 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5334509) (@lem5334508 _69707)). Qed.
Lemma lem5334511 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5334512 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5334510 _69707) (@lem5334511)). Qed.
Lemma lem5334513 (_69707 : int) : (term706 _69707) = term710.
Proof. exact (TRANS (@lem5334402 _69707) (@lem5334512 _69707)). Qed.
Lemma lem5334514 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5334515 (_69707 : int) : (term706 _69707) = term355.
Proof. exact (TRANS (@lem5334513 _69707) (@lem5334514)). Qed.
Lemma lem5334516 (_69704 : int) (_69707 : int) : (term686 _69704 _69707) = term710.
Proof. exact (MK_COMB (@lem5334401 _69704) (@lem5334515 _69707)). Qed.
Lemma lem5334517 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term710.
Proof. exact (TRANS (@lem5334293 _69704 _69707) (@lem5334516 _69704 _69707)). Qed.
Lemma lem5334518 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5334519 (_69704 : int) (_69707 : int) : (term685 _69704 _69707) = term355.
Proof. exact (TRANS (@lem5334517 _69704 _69707) (@lem5334518)). Qed.
Lemma lem5334520 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334521 (_69704 : int) (_69707 : int) : (term711 _69704 _69707) = term712.
Proof. exact (MK_COMB (@lem5334520) (@lem5334519 _69704 _69707)). Qed.
Lemma lem5334522 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334523 (_69704 : int) (_69707 : int) : (term684 _69704 _69707) = term713.
Proof. exact (MK_COMB (@lem5334521 _69704 _69707) (@lem5334522)). Qed.
Lemma lem5334524 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : term713.
Proof. exact (EQ_MP (@lem5334523 _69704 _69707) (@lem5334292 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334526 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5334527 : term713 = term714.
Proof. exact (@lem5334526 term293 term355). Qed.
Lemma lem5334529 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334530 : term355 = term356.
Proof. exact (@lem5334529 term157). Qed.
Lemma lem5334532 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334533 : term293 = term352.
Proof. exact (@lem5334532 (NUMERAL 0)). Qed.
Lemma lem5334534 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5334535 : term295 = term715.
Proof. exact (MK_COMB (@lem5334534) (@lem5334533)). Qed.
Lemma lem5334536 : term714 = term716.
Proof. exact (MK_COMB (@lem5334535) (@lem5334530)). Qed.
Lemma lem5334537 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5334539 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334540 : term431 = term432.
Proof. exact (@lem5334539 (NUMERAL 0) term157). Qed.
Lemma lem5334541 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334542 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334543 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334542 h1) (fun h1 : term432 = True => @lem5334541)). Qed.
Lemma lem5334544 : term432 = True.
Proof. exact (EQ_MP (@lem5334543) (@lem5334541)). Qed.
Lemma lem5334545 : term431 = True.
Proof. exact (TRANS (@lem5334540) (@lem5334544)). Qed.
Lemma lem5334546 : True = term431.
Proof. exact (SYM (@lem5334545)). Qed.
Lemma lem5334547 : term431.
Proof. exact (EQ_MP (@lem5334546) (@lem0)). Qed.
Lemma lem5334548 : term718.
Proof. exact (@lem5334537 (@lem5334547)). Qed.
Lemma lem5334550 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334551 : term431 = term432.
Proof. exact (@lem5334550 (NUMERAL 0) term157). Qed.
Lemma lem5334552 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334553 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334554 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334553 h1) (fun h1 : term432 = True => @lem5334552)). Qed.
Lemma lem5334555 : term432 = True.
Proof. exact (EQ_MP (@lem5334554) (@lem5334552)). Qed.
Lemma lem5334556 : term431 = True.
Proof. exact (TRANS (@lem5334551) (@lem5334555)). Qed.
Lemma lem5334557 : True = term431.
Proof. exact (SYM (@lem5334556)). Qed.
Lemma lem5334558 : term431.
Proof. exact (EQ_MP (@lem5334557) (@lem0)). Qed.
Lemma lem5334559 : term716 = term719.
Proof. exact (@lem5334548 (@lem5334558)). Qed.
Lemma lem5334561 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334562 : term398 = term403.
Proof. exact (@lem5334561 term157 term157). Qed.
Lemma lem5334563 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334564 : term367 = term157.
Proof. exact (EQ_MP (@lem5334563) (@lem940073)). Qed.
Lemma lem5334565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334566 : term365 = term305.
Proof. exact (MK_COMB (@lem5334565) (@lem5334564)). Qed.
Lemma lem5334567 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5334568 : term403 = term355.
Proof. exact (MK_COMB (@lem5334567) (@lem5334566)). Qed.
Lemma lem5334569 : term398 = term355.
Proof. exact (TRANS (@lem5334562) (@lem5334568)). Qed.
Lemma lem5334571 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334572 : term443 = term293.
Proof. exact (@lem5334571 term157). Qed.
Lemma lem5334573 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5334574 : term720 = term295.
Proof. exact (MK_COMB (@lem5334573) (@lem5334572)). Qed.
Lemma lem5334575 : term719 = term714.
Proof. exact (MK_COMB (@lem5334574) (@lem5334569)). Qed.
Lemma lem5334577 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5334578 : term714 = term723.
Proof. exact (@lem5334577 (NUMERAL 0) term157). Qed.
Lemma lem5334579 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334580 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5334581 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334580 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5334579)). Qed.
Lemma lem5334582 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5334581) (@lem5334579)). Qed.
Lemma lem5334583 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5334584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5334585 : term724 = (and True).
Proof. exact (MK_COMB (@lem5334584) (@lem5334583)). Qed.
Lemma lem5334586 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5334585) (@lem5334582)). Qed.
Lemma lem5334588 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5334589 : term723 = False.
Proof. exact (TRANS (@lem5334586) (@lem5334588)). Qed.
Lemma lem5334590 : term714 = False.
Proof. exact (TRANS (@lem5334578) (@lem5334589)). Qed.
Lemma lem5334591 : term719 = False.
Proof. exact (TRANS (@lem5334575) (@lem5334590)). Qed.
Lemma lem5334592 : term716 = False.
Proof. exact (TRANS (@lem5334559) (@lem5334591)). Qed.
Lemma lem5334593 : term714 = False.
Proof. exact (TRANS (@lem5334536) (@lem5334592)). Qed.
Lemma lem5334594 : term713 = False.
Proof. exact (TRANS (@lem5334527) (@lem5334593)). Qed.
Lemma lem5334595 (_69705 : int) (_69706 : int) (_69704 : int) (_69707 : int) (h1 : term745 _69705 _69706 _69704 _69707) : False.
Proof. exact (EQ_MP (@lem5334594) (@lem5334524 _69705 _69706 _69704 _69707 h1)). Qed.
Lemma lem5334596 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term746 _69706 _69705 _69704 _69707.
Proof. exact (h1). Qed.
Lemma lem5334597 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term641 _69706 _69705 _69704 _69707.
Proof. exact (proj2 (@lem5334596 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334599 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term610 _69706 _69705 _69704 _69707.
Proof. exact (proj2 (@lem5334597 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334601 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term579 _69706 _69705 _69704 _69707.
Proof. exact (proj2 (@lem5334599 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334603 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term548 _69706 _69705 _69704 _69707.
Proof. exact (proj2 (@lem5334601 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334605 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term517 _69706 _69705 _69704 _69707.
Proof. exact (proj2 (@lem5334603 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334606 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term391 _69704 _69705 _69706.
Proof. exact (proj1 (@lem5334603 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334608 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term383 _69704 _69706.
Proof. exact (proj1 (@lem5334606 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334609 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term411 _69704 _69707.
Proof. exact (proj2 (@lem5334605 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334610 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term460 _69706 _69705 _69707.
Proof. exact (proj1 (@lem5334605 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334612 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term414 _69706 _69707.
Proof. exact (proj1 (@lem5334610 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334614 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5334615 : term662 = term431.
Proof. exact (@lem5334614 term293 term305). Qed.
Lemma lem5334617 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334618 : term305 = term397.
Proof. exact (@lem5334617 term157). Qed.
Lemma lem5334620 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334621 : term293 = term352.
Proof. exact (@lem5334620 (NUMERAL 0)). Qed.
Lemma lem5334622 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334623 : term663 = term664.
Proof. exact (MK_COMB (@lem5334622) (@lem5334621)). Qed.
Lemma lem5334624 : term431 = term665.
Proof. exact (MK_COMB (@lem5334623) (@lem5334618)). Qed.
Lemma lem5334625 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5334627 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334628 : term431 = term432.
Proof. exact (@lem5334627 (NUMERAL 0) term157). Qed.
Lemma lem5334629 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334630 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334631 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334630 h1) (fun h1 : term432 = True => @lem5334629)). Qed.
Lemma lem5334632 : term432 = True.
Proof. exact (EQ_MP (@lem5334631) (@lem5334629)). Qed.
Lemma lem5334633 : term431 = True.
Proof. exact (TRANS (@lem5334628) (@lem5334632)). Qed.
Lemma lem5334634 : True = term431.
Proof. exact (SYM (@lem5334633)). Qed.
Lemma lem5334635 : term431.
Proof. exact (EQ_MP (@lem5334634) (@lem0)). Qed.
Lemma lem5334636 : term667.
Proof. exact (@lem5334625 (@lem5334635)). Qed.
Lemma lem5334638 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334639 : term431 = term432.
Proof. exact (@lem5334638 (NUMERAL 0) term157). Qed.
Lemma lem5334640 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334641 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334642 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334641 h1) (fun h1 : term432 = True => @lem5334640)). Qed.
Lemma lem5334643 : term432 = True.
Proof. exact (EQ_MP (@lem5334642) (@lem5334640)). Qed.
Lemma lem5334644 : term431 = True.
Proof. exact (TRANS (@lem5334639) (@lem5334643)). Qed.
Lemma lem5334645 : True = term431.
Proof. exact (SYM (@lem5334644)). Qed.
Lemma lem5334646 : term431.
Proof. exact (EQ_MP (@lem5334645) (@lem0)). Qed.
Lemma lem5334647 : term665 = term668.
Proof. exact (@lem5334636 (@lem5334646)). Qed.
Lemma lem5334649 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334650 : term364 = term365.
Proof. exact (@lem5334649 term157 term157). Qed.
Lemma lem5334651 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334652 : term367 = term157.
Proof. exact (EQ_MP (@lem5334651) (@lem940073)). Qed.
Lemma lem5334653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334654 : term365 = term305.
Proof. exact (MK_COMB (@lem5334653) (@lem5334652)). Qed.
Lemma lem5334655 : term364 = term305.
Proof. exact (TRANS (@lem5334650) (@lem5334654)). Qed.
Lemma lem5334657 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334658 : term443 = term293.
Proof. exact (@lem5334657 term157). Qed.
Lemma lem5334659 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334660 : term669 = term663.
Proof. exact (MK_COMB (@lem5334659) (@lem5334658)). Qed.
Lemma lem5334661 : term668 = term431.
Proof. exact (MK_COMB (@lem5334660) (@lem5334655)). Qed.
Lemma lem5334663 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334664 : term431 = term432.
Proof. exact (@lem5334663 (NUMERAL 0) term157). Qed.
Lemma lem5334665 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334666 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334667 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334666 h1) (fun h1 : term432 = True => @lem5334665)). Qed.
Lemma lem5334668 : term432 = True.
Proof. exact (EQ_MP (@lem5334667) (@lem5334665)). Qed.
Lemma lem5334669 : term431 = True.
Proof. exact (TRANS (@lem5334664) (@lem5334668)). Qed.
Lemma lem5334670 : term668 = True.
Proof. exact (TRANS (@lem5334661) (@lem5334669)). Qed.
Lemma lem5334671 : term665 = True.
Proof. exact (TRANS (@lem5334647) (@lem5334670)). Qed.
Lemma lem5334672 : term431 = True.
Proof. exact (TRANS (@lem5334624) (@lem5334671)). Qed.
Lemma lem5334673 : term662 = True.
Proof. exact (TRANS (@lem5334615) (@lem5334672)). Qed.
Lemma lem5334674 : True = term662.
Proof. exact (SYM (@lem5334673)). Qed.
Lemma lem5334675 : term662.
Proof. exact (EQ_MP (@lem5334674) (@lem0)). Qed.
Lemma lem5334676 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term731 _69706 _69707.
Proof. exact (conj (@lem5334675) (@lem5334612 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334678 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5334679 (_69706 : int) (_69707 : int) : term732 _69706 _69707.
Proof. exact (@lem5334678 term305 (term412 _69706 _69707)). Qed.
Lemma lem5334680 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term733 _69706 _69707.
Proof. exact (@lem5334679 _69706 _69707 (@lem5334676 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334681 (_69706 : int) (_69707 : int) : (term734 _69706 _69707) = (term412 _69706 _69707).
Proof. exact (@lem1982733 (term412 _69706 _69707)). Qed.
Lemma lem5334682 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334683 (_69706 : int) (_69707 : int) : (term735 _69706 _69707) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5334682) (@lem5334681 _69706 _69707)). Qed.
Lemma lem5334684 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334685 (_69706 : int) (_69707 : int) : (term733 _69706 _69707) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5334683 _69706 _69707) (@lem5334684)). Qed.
Lemma lem5334686 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term414 _69706 _69707.
Proof. exact (EQ_MP (@lem5334685 _69706 _69707) (@lem5334680 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334688 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5334689 : term662 = term431.
Proof. exact (@lem5334688 term293 term305). Qed.
Lemma lem5334691 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334692 : term305 = term397.
Proof. exact (@lem5334691 term157). Qed.
Lemma lem5334694 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334695 : term293 = term352.
Proof. exact (@lem5334694 (NUMERAL 0)). Qed.
Lemma lem5334696 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334697 : term663 = term664.
Proof. exact (MK_COMB (@lem5334696) (@lem5334695)). Qed.
Lemma lem5334698 : term431 = term665.
Proof. exact (MK_COMB (@lem5334697) (@lem5334692)). Qed.
Lemma lem5334699 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5334701 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334702 : term431 = term432.
Proof. exact (@lem5334701 (NUMERAL 0) term157). Qed.
Lemma lem5334703 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334704 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334705 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334704 h1) (fun h1 : term432 = True => @lem5334703)). Qed.
Lemma lem5334706 : term432 = True.
Proof. exact (EQ_MP (@lem5334705) (@lem5334703)). Qed.
Lemma lem5334707 : term431 = True.
Proof. exact (TRANS (@lem5334702) (@lem5334706)). Qed.
Lemma lem5334708 : True = term431.
Proof. exact (SYM (@lem5334707)). Qed.
Lemma lem5334709 : term431.
Proof. exact (EQ_MP (@lem5334708) (@lem0)). Qed.
Lemma lem5334710 : term667.
Proof. exact (@lem5334699 (@lem5334709)). Qed.
Lemma lem5334712 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334713 : term431 = term432.
Proof. exact (@lem5334712 (NUMERAL 0) term157). Qed.
Lemma lem5334714 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334715 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334716 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334715 h1) (fun h1 : term432 = True => @lem5334714)). Qed.
Lemma lem5334717 : term432 = True.
Proof. exact (EQ_MP (@lem5334716) (@lem5334714)). Qed.
Lemma lem5334718 : term431 = True.
Proof. exact (TRANS (@lem5334713) (@lem5334717)). Qed.
Lemma lem5334719 : True = term431.
Proof. exact (SYM (@lem5334718)). Qed.
Lemma lem5334720 : term431.
Proof. exact (EQ_MP (@lem5334719) (@lem0)). Qed.
Lemma lem5334721 : term665 = term668.
Proof. exact (@lem5334710 (@lem5334720)). Qed.
Lemma lem5334723 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334724 : term364 = term365.
Proof. exact (@lem5334723 term157 term157). Qed.
Lemma lem5334725 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334726 : term367 = term157.
Proof. exact (EQ_MP (@lem5334725) (@lem940073)). Qed.
Lemma lem5334727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334728 : term365 = term305.
Proof. exact (MK_COMB (@lem5334727) (@lem5334726)). Qed.
Lemma lem5334729 : term364 = term305.
Proof. exact (TRANS (@lem5334724) (@lem5334728)). Qed.
Lemma lem5334731 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334732 : term443 = term293.
Proof. exact (@lem5334731 term157). Qed.
Lemma lem5334733 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334734 : term669 = term663.
Proof. exact (MK_COMB (@lem5334733) (@lem5334732)). Qed.
Lemma lem5334735 : term668 = term431.
Proof. exact (MK_COMB (@lem5334734) (@lem5334729)). Qed.
Lemma lem5334737 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334738 : term431 = term432.
Proof. exact (@lem5334737 (NUMERAL 0) term157). Qed.
Lemma lem5334739 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334740 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334741 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334740 h1) (fun h1 : term432 = True => @lem5334739)). Qed.
Lemma lem5334742 : term432 = True.
Proof. exact (EQ_MP (@lem5334741) (@lem5334739)). Qed.
Lemma lem5334743 : term431 = True.
Proof. exact (TRANS (@lem5334738) (@lem5334742)). Qed.
Lemma lem5334744 : term668 = True.
Proof. exact (TRANS (@lem5334735) (@lem5334743)). Qed.
Lemma lem5334745 : term665 = True.
Proof. exact (TRANS (@lem5334721) (@lem5334744)). Qed.
Lemma lem5334746 : term431 = True.
Proof. exact (TRANS (@lem5334698) (@lem5334745)). Qed.
Lemma lem5334747 : term662 = True.
Proof. exact (TRANS (@lem5334689) (@lem5334746)). Qed.
Lemma lem5334748 : True = term662.
Proof. exact (SYM (@lem5334747)). Qed.
Lemma lem5334749 : term662.
Proof. exact (EQ_MP (@lem5334748) (@lem0)). Qed.
Lemma lem5334750 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term670 _69704 _69707.
Proof. exact (conj (@lem5334749) (@lem5334609 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334752 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5334753 (_69704 : int) (_69707 : int) : term672 _69704 _69707.
Proof. exact (@lem5334752 term305 (term408 _69704 _69707)). Qed.
Lemma lem5334754 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term673 _69704 _69707.
Proof. exact (@lem5334753 _69704 _69707 (@lem5334750 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334755 (_69704 : int) (_69707 : int) : (term674 _69704 _69707) = (term408 _69704 _69707).
Proof. exact (@lem1982733 (term408 _69704 _69707)). Qed.
Lemma lem5334756 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334757 (_69704 : int) (_69707 : int) : (term675 _69704 _69707) = (term410 _69704 _69707).
Proof. exact (MK_COMB (@lem5334756) (@lem5334755 _69704 _69707)). Qed.
Lemma lem5334758 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334759 (_69704 : int) (_69707 : int) : (term673 _69704 _69707) = (term411 _69704 _69707).
Proof. exact (MK_COMB (@lem5334757 _69704 _69707) (@lem5334758)). Qed.
Lemma lem5334760 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term411 _69704 _69707.
Proof. exact (EQ_MP (@lem5334759 _69704 _69707) (@lem5334754 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334762 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5334763 : term662 = term431.
Proof. exact (@lem5334762 term293 term305). Qed.
Lemma lem5334765 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334766 : term305 = term397.
Proof. exact (@lem5334765 term157). Qed.
Lemma lem5334768 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334769 : term293 = term352.
Proof. exact (@lem5334768 (NUMERAL 0)). Qed.
Lemma lem5334770 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334771 : term663 = term664.
Proof. exact (MK_COMB (@lem5334770) (@lem5334769)). Qed.
Lemma lem5334772 : term431 = term665.
Proof. exact (MK_COMB (@lem5334771) (@lem5334766)). Qed.
Lemma lem5334773 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5334775 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334776 : term431 = term432.
Proof. exact (@lem5334775 (NUMERAL 0) term157). Qed.
Lemma lem5334777 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334778 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334779 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334778 h1) (fun h1 : term432 = True => @lem5334777)). Qed.
Lemma lem5334780 : term432 = True.
Proof. exact (EQ_MP (@lem5334779) (@lem5334777)). Qed.
Lemma lem5334781 : term431 = True.
Proof. exact (TRANS (@lem5334776) (@lem5334780)). Qed.
Lemma lem5334782 : True = term431.
Proof. exact (SYM (@lem5334781)). Qed.
Lemma lem5334783 : term431.
Proof. exact (EQ_MP (@lem5334782) (@lem0)). Qed.
Lemma lem5334784 : term667.
Proof. exact (@lem5334773 (@lem5334783)). Qed.
Lemma lem5334786 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334787 : term431 = term432.
Proof. exact (@lem5334786 (NUMERAL 0) term157). Qed.
Lemma lem5334788 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334789 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334790 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334789 h1) (fun h1 : term432 = True => @lem5334788)). Qed.
Lemma lem5334791 : term432 = True.
Proof. exact (EQ_MP (@lem5334790) (@lem5334788)). Qed.
Lemma lem5334792 : term431 = True.
Proof. exact (TRANS (@lem5334787) (@lem5334791)). Qed.
Lemma lem5334793 : True = term431.
Proof. exact (SYM (@lem5334792)). Qed.
Lemma lem5334794 : term431.
Proof. exact (EQ_MP (@lem5334793) (@lem0)). Qed.
Lemma lem5334795 : term665 = term668.
Proof. exact (@lem5334784 (@lem5334794)). Qed.
Lemma lem5334797 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334798 : term364 = term365.
Proof. exact (@lem5334797 term157 term157). Qed.
Lemma lem5334799 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334800 : term367 = term157.
Proof. exact (EQ_MP (@lem5334799) (@lem940073)). Qed.
Lemma lem5334801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334802 : term365 = term305.
Proof. exact (MK_COMB (@lem5334801) (@lem5334800)). Qed.
Lemma lem5334803 : term364 = term305.
Proof. exact (TRANS (@lem5334798) (@lem5334802)). Qed.
Lemma lem5334805 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334806 : term443 = term293.
Proof. exact (@lem5334805 term157). Qed.
Lemma lem5334807 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5334808 : term669 = term663.
Proof. exact (MK_COMB (@lem5334807) (@lem5334806)). Qed.
Lemma lem5334809 : term668 = term431.
Proof. exact (MK_COMB (@lem5334808) (@lem5334803)). Qed.
Lemma lem5334811 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334812 : term431 = term432.
Proof. exact (@lem5334811 (NUMERAL 0) term157). Qed.
Lemma lem5334813 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334814 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334815 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334814 h1) (fun h1 : term432 = True => @lem5334813)). Qed.
Lemma lem5334816 : term432 = True.
Proof. exact (EQ_MP (@lem5334815) (@lem5334813)). Qed.
Lemma lem5334817 : term431 = True.
Proof. exact (TRANS (@lem5334812) (@lem5334816)). Qed.
Lemma lem5334818 : term668 = True.
Proof. exact (TRANS (@lem5334809) (@lem5334817)). Qed.
Lemma lem5334819 : term665 = True.
Proof. exact (TRANS (@lem5334795) (@lem5334818)). Qed.
Lemma lem5334820 : term431 = True.
Proof. exact (TRANS (@lem5334772) (@lem5334819)). Qed.
Lemma lem5334821 : term662 = True.
Proof. exact (TRANS (@lem5334763) (@lem5334820)). Qed.
Lemma lem5334822 : True = term662.
Proof. exact (SYM (@lem5334821)). Qed.
Lemma lem5334823 : term662.
Proof. exact (EQ_MP (@lem5334822) (@lem0)). Qed.
Lemma lem5334824 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term747 _69704 _69706.
Proof. exact (conj (@lem5334823) (@lem5334608 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334826 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5334827 (_69704 : int) (_69706 : int) : term748 _69704 _69706.
Proof. exact (@lem5334826 term305 (term379 _69704 _69706)). Qed.
Lemma lem5334828 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term749 _69704 _69706.
Proof. exact (@lem5334827 _69704 _69706 (@lem5334824 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334829 (_69704 : int) (_69706 : int) : (term750 _69704 _69706) = (term379 _69704 _69706).
Proof. exact (@lem1982733 (term379 _69704 _69706)). Qed.
Lemma lem5334830 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5334831 (_69704 : int) (_69706 : int) : (term751 _69704 _69706) = (term382 _69704 _69706).
Proof. exact (MK_COMB (@lem5334830) (@lem5334829 _69704 _69706)). Qed.
Lemma lem5334832 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5334833 (_69704 : int) (_69706 : int) : (term749 _69704 _69706) = (term383 _69704 _69706).
Proof. exact (MK_COMB (@lem5334831 _69704 _69706) (@lem5334832)). Qed.
Lemma lem5334834 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term383 _69704 _69706.
Proof. exact (EQ_MP (@lem5334833 _69704 _69706) (@lem5334828 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334835 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term752 _69706 _69704 _69707.
Proof. exact (conj (@lem5334834 _69706 _69705 _69704 _69707 h1) (@lem5334760 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334837 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5334838 (_69706 : int) (_69704 : int) (_69707 : int) : term753 _69706 _69704 _69707.
Proof. exact (@lem5334837 (term379 _69704 _69706) (term408 _69704 _69707)). Qed.
Lemma lem5334839 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term754 _69706 _69704 _69707.
Proof. exact (@lem5334838 _69706 _69704 _69707 (@lem5334835 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5334840 (_69704 : int) (_69706 : int) (_69707 : int) : (term755 _69706 _69704 _69707) = (term756 _69704 _69706 _69707).
Proof. exact (@lem1982753 (term380 _69704) (real_of_int _69704) (term307 _69706) (term407 _69707)). Qed.
Lemma lem5334841 (_69704 : int) : (term687 _69704) = (term688 _69704).
Proof. exact (@lem1982713 term355 (real_of_int _69704)). Qed.
Lemma lem5334843 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334844 : term305 = term397.
Proof. exact (@lem5334843 term157). Qed.
Lemma lem5334846 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334847 : term355 = term356.
Proof. exact (@lem5334846 term157). Qed.
Lemma lem5334848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334849 : term689 = term690.
Proof. exact (MK_COMB (@lem5334848) (@lem5334847)). Qed.
Lemma lem5334850 : term691 = term692.
Proof. exact (MK_COMB (@lem5334849) (@lem5334844)). Qed.
Lemma lem5334851 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5334853 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334854 : term431 = term432.
Proof. exact (@lem5334853 (NUMERAL 0) term157). Qed.
Lemma lem5334855 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334856 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334857 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334856 h1) (fun h1 : term432 = True => @lem5334855)). Qed.
Lemma lem5334858 : term432 = True.
Proof. exact (EQ_MP (@lem5334857) (@lem5334855)). Qed.
Lemma lem5334859 : term431 = True.
Proof. exact (TRANS (@lem5334854) (@lem5334858)). Qed.
Lemma lem5334860 : True = term431.
Proof. exact (SYM (@lem5334859)). Qed.
Lemma lem5334861 : term431.
Proof. exact (EQ_MP (@lem5334860) (@lem0)). Qed.
Lemma lem5334862 : term694.
Proof. exact (@lem5334851 (@lem5334861)). Qed.
Lemma lem5334864 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334865 : term431 = term432.
Proof. exact (@lem5334864 (NUMERAL 0) term157). Qed.
Lemma lem5334866 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334867 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334868 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334867 h1) (fun h1 : term432 = True => @lem5334866)). Qed.
Lemma lem5334869 : term432 = True.
Proof. exact (EQ_MP (@lem5334868) (@lem5334866)). Qed.
Lemma lem5334870 : term431 = True.
Proof. exact (TRANS (@lem5334865) (@lem5334869)). Qed.
Lemma lem5334871 : True = term431.
Proof. exact (SYM (@lem5334870)). Qed.
Lemma lem5334872 : term431.
Proof. exact (EQ_MP (@lem5334871) (@lem0)). Qed.
Lemma lem5334873 : term695.
Proof. exact (@lem5334862 (@lem5334872)). Qed.
Lemma lem5334875 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334876 : term431 = term432.
Proof. exact (@lem5334875 (NUMERAL 0) term157). Qed.
Lemma lem5334877 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334878 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334879 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334878 h1) (fun h1 : term432 = True => @lem5334877)). Qed.
Lemma lem5334880 : term432 = True.
Proof. exact (EQ_MP (@lem5334879) (@lem5334877)). Qed.
Lemma lem5334881 : term431 = True.
Proof. exact (TRANS (@lem5334876) (@lem5334880)). Qed.
Lemma lem5334882 : True = term431.
Proof. exact (SYM (@lem5334881)). Qed.
Lemma lem5334883 : term431.
Proof. exact (EQ_MP (@lem5334882) (@lem0)). Qed.
Lemma lem5334884 : term696.
Proof. exact (@lem5334873 (@lem5334883)). Qed.
Lemma lem5334886 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334887 : term364 = term365.
Proof. exact (@lem5334886 term157 term157). Qed.
Lemma lem5334888 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334889 : term367 = term157.
Proof. exact (EQ_MP (@lem5334888) (@lem940073)). Qed.
Lemma lem5334890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334891 : term365 = term305.
Proof. exact (MK_COMB (@lem5334890) (@lem5334889)). Qed.
Lemma lem5334892 : term364 = term305.
Proof. exact (TRANS (@lem5334887) (@lem5334891)). Qed.
Lemma lem5334894 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334895 : term398 = term403.
Proof. exact (@lem5334894 term157 term157). Qed.
Lemma lem5334896 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334897 : term367 = term157.
Proof. exact (EQ_MP (@lem5334896) (@lem940073)). Qed.
Lemma lem5334898 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334899 : term365 = term305.
Proof. exact (MK_COMB (@lem5334898) (@lem5334897)). Qed.
Lemma lem5334900 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5334901 : term403 = term355.
Proof. exact (MK_COMB (@lem5334900) (@lem5334899)). Qed.
Lemma lem5334902 : term398 = term355.
Proof. exact (TRANS (@lem5334895) (@lem5334901)). Qed.
Lemma lem5334903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334904 : term697 = term689.
Proof. exact (MK_COMB (@lem5334903) (@lem5334902)). Qed.
Lemma lem5334905 : term698 = term691.
Proof. exact (MK_COMB (@lem5334904) (@lem5334892)). Qed.
Lemma lem5334907 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5334908 : term691 = term293.
Proof. exact (@lem5334907 term157). Qed.
Lemma lem5334909 : term698 = term293.
Proof. exact (TRANS (@lem5334905) (@lem5334908)). Qed.
Lemma lem5334910 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334911 : term700 = term441.
Proof. exact (MK_COMB (@lem5334910) (@lem5334909)). Qed.
Lemma lem5334912 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5334913 : term701 = term443.
Proof. exact (MK_COMB (@lem5334911) (@lem5334912)). Qed.
Lemma lem5334915 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334916 : term443 = term293.
Proof. exact (@lem5334915 term157). Qed.
Lemma lem5334917 : term701 = term293.
Proof. exact (TRANS (@lem5334913) (@lem5334916)). Qed.
Lemma lem5334919 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5334920 : term364 = term365.
Proof. exact (@lem5334919 term157 term157). Qed.
Lemma lem5334921 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334922 : term367 = term157.
Proof. exact (EQ_MP (@lem5334921) (@lem940073)). Qed.
Lemma lem5334923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5334924 : term365 = term305.
Proof. exact (MK_COMB (@lem5334923) (@lem5334922)). Qed.
Lemma lem5334925 : term364 = term305.
Proof. exact (TRANS (@lem5334920) (@lem5334924)). Qed.
Lemma lem5334926 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5334927 : term445 = term443.
Proof. exact (MK_COMB (@lem5334926) (@lem5334925)). Qed.
Lemma lem5334929 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5334930 : term443 = term293.
Proof. exact (@lem5334929 term157). Qed.
Lemma lem5334931 : term445 = term293.
Proof. exact (TRANS (@lem5334927) (@lem5334930)). Qed.
Lemma lem5334932 : term293 = term445.
Proof. exact (SYM (@lem5334931)). Qed.
Lemma lem5334933 : term701 = term445.
Proof. exact (TRANS (@lem5334917) (@lem5334932)). Qed.
Lemma lem5334934 : term692 = term352.
Proof. exact (@lem5334884 (@lem5334933)). Qed.
Lemma lem5334935 : term691 = term352.
Proof. exact (TRANS (@lem5334850) (@lem5334934)). Qed.
Lemma lem5334937 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5334938 : term352 = term293.
Proof. exact (@lem5334937 term293). Qed.
Lemma lem5334939 : term691 = term293.
Proof. exact (TRANS (@lem5334935) (@lem5334938)). Qed.
Lemma lem5334940 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5334941 : term702 = term441.
Proof. exact (MK_COMB (@lem5334940) (@lem5334939)). Qed.
Lemma lem5334942 (_69704 : int) : (real_of_int _69704) = (real_of_int _69704).
Proof. exact (eq_refl (real_of_int _69704)). Qed.
Lemma lem5334943 (_69704 : int) : (term688 _69704) = (term703 _69704).
Proof. exact (MK_COMB (@lem5334941) (@lem5334942 _69704)). Qed.
Lemma lem5334944 (_69704 : int) : (term687 _69704) = (term703 _69704).
Proof. exact (TRANS (@lem5334841 _69704) (@lem5334943 _69704)). Qed.
Lemma lem5334945 (_69704 : int) : (term703 _69704) = term293.
Proof. exact (@lem1982719 (real_of_int _69704)). Qed.
Lemma lem5334946 (_69704 : int) : (term687 _69704) = term293.
Proof. exact (TRANS (@lem5334944 _69704) (@lem5334945 _69704)). Qed.
Lemma lem5334947 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334948 (_69704 : int) : (term704 _69704) = term705.
Proof. exact (MK_COMB (@lem5334947) (@lem5334946 _69704)). Qed.
Lemma lem5334949 (_69706 : int) (_69707 : int) : (term421 _69706 _69707) = (term422 _69706 _69707).
Proof. exact (@lem1982755 (real_of_int _69706) term305 (term407 _69707)). Qed.
Lemma lem5334950 (_69707 : int) : (term423 _69707) = (term424 _69707).
Proof. exact (@lem1982757 (term380 _69707) term305 term355). Qed.
Lemma lem5334952 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5334953 : term355 = term356.
Proof. exact (@lem5334952 term157). Qed.
Lemma lem5334955 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5334956 : term305 = term397.
Proof. exact (@lem5334955 term157). Qed.
Lemma lem5334957 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5334958 : term425 = term426.
Proof. exact (MK_COMB (@lem5334957) (@lem5334956)). Qed.
Lemma lem5334959 : term427 = term428.
Proof. exact (MK_COMB (@lem5334958) (@lem5334953)). Qed.
Lemma lem5334960 : term429.
Proof. exact (@lem1981473 term305 term305 term355 term305 term293 term305). Qed.
Lemma lem5334962 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334963 : term431 = term432.
Proof. exact (@lem5334962 (NUMERAL 0) term157). Qed.
Lemma lem5334964 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334965 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334966 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334965 h1) (fun h1 : term432 = True => @lem5334964)). Qed.
Lemma lem5334967 : term432 = True.
Proof. exact (EQ_MP (@lem5334966) (@lem5334964)). Qed.
Lemma lem5334968 : term431 = True.
Proof. exact (TRANS (@lem5334963) (@lem5334967)). Qed.
Lemma lem5334969 : True = term431.
Proof. exact (SYM (@lem5334968)). Qed.
Lemma lem5334970 : term431.
Proof. exact (EQ_MP (@lem5334969) (@lem0)). Qed.
Lemma lem5334971 : term434.
Proof. exact (@lem5334960 (@lem5334970)). Qed.
Lemma lem5334973 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334974 : term431 = term432.
Proof. exact (@lem5334973 (NUMERAL 0) term157). Qed.
Lemma lem5334975 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334976 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334977 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334976 h1) (fun h1 : term432 = True => @lem5334975)). Qed.
Lemma lem5334978 : term432 = True.
Proof. exact (EQ_MP (@lem5334977) (@lem5334975)). Qed.
Lemma lem5334979 : term431 = True.
Proof. exact (TRANS (@lem5334974) (@lem5334978)). Qed.
Lemma lem5334980 : True = term431.
Proof. exact (SYM (@lem5334979)). Qed.
Lemma lem5334981 : term431.
Proof. exact (EQ_MP (@lem5334980) (@lem0)). Qed.
Lemma lem5334982 : term435.
Proof. exact (@lem5334971 (@lem5334981)). Qed.
Lemma lem5334984 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5334985 : term431 = term432.
Proof. exact (@lem5334984 (NUMERAL 0) term157). Qed.
Lemma lem5334986 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5334987 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5334988 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5334987 h1) (fun h1 : term432 = True => @lem5334986)). Qed.
Lemma lem5334989 : term432 = True.
Proof. exact (EQ_MP (@lem5334988) (@lem5334986)). Qed.
Lemma lem5334990 : term431 = True.
Proof. exact (TRANS (@lem5334985) (@lem5334989)). Qed.
Lemma lem5334991 : True = term431.
Proof. exact (SYM (@lem5334990)). Qed.
Lemma lem5334992 : term431.
Proof. exact (EQ_MP (@lem5334991) (@lem0)). Qed.
Lemma lem5334993 : term436.
Proof. exact (@lem5334982 (@lem5334992)). Qed.
Lemma lem5334995 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5334996 : term398 = term403.
Proof. exact (@lem5334995 term157 term157). Qed.
Lemma lem5334997 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5334998 : term367 = term157.
Proof. exact (EQ_MP (@lem5334997) (@lem940073)). Qed.
Lemma lem5334999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335000 : term365 = term305.
Proof. exact (MK_COMB (@lem5334999) (@lem5334998)). Qed.
Lemma lem5335001 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335002 : term403 = term355.
Proof. exact (MK_COMB (@lem5335001) (@lem5335000)). Qed.
Lemma lem5335003 : term398 = term355.
Proof. exact (TRANS (@lem5334996) (@lem5335002)). Qed.
Lemma lem5335005 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335006 : term364 = term365.
Proof. exact (@lem5335005 term157 term157). Qed.
Lemma lem5335007 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335008 : term367 = term157.
Proof. exact (EQ_MP (@lem5335007) (@lem940073)). Qed.
Lemma lem5335009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335010 : term365 = term305.
Proof. exact (MK_COMB (@lem5335009) (@lem5335008)). Qed.
Lemma lem5335011 : term364 = term305.
Proof. exact (TRANS (@lem5335006) (@lem5335010)). Qed.
Lemma lem5335012 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335013 : term437 = term425.
Proof. exact (MK_COMB (@lem5335012) (@lem5335011)). Qed.
Lemma lem5335014 : term438 = term427.
Proof. exact (MK_COMB (@lem5335013) (@lem5335003)). Qed.
Lemma lem5335016 (m : nat) : (term439 m) = term293.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5335017 : term427 = term293.
Proof. exact (@lem5335016 term157). Qed.
Lemma lem5335018 : term438 = term293.
Proof. exact (TRANS (@lem5335014) (@lem5335017)). Qed.
Lemma lem5335019 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335020 : term440 = term441.
Proof. exact (MK_COMB (@lem5335019) (@lem5335018)). Qed.
Lemma lem5335021 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5335022 : term442 = term443.
Proof. exact (MK_COMB (@lem5335020) (@lem5335021)). Qed.
Lemma lem5335024 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335025 : term443 = term293.
Proof. exact (@lem5335024 term157). Qed.
Lemma lem5335026 : term442 = term293.
Proof. exact (TRANS (@lem5335022) (@lem5335025)). Qed.
Lemma lem5335028 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335029 : term364 = term365.
Proof. exact (@lem5335028 term157 term157). Qed.
Lemma lem5335030 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335031 : term367 = term157.
Proof. exact (EQ_MP (@lem5335030) (@lem940073)). Qed.
Lemma lem5335032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335033 : term365 = term305.
Proof. exact (MK_COMB (@lem5335032) (@lem5335031)). Qed.
Lemma lem5335034 : term364 = term305.
Proof. exact (TRANS (@lem5335029) (@lem5335033)). Qed.
Lemma lem5335035 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5335036 : term445 = term443.
Proof. exact (MK_COMB (@lem5335035) (@lem5335034)). Qed.
Lemma lem5335038 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335039 : term443 = term293.
Proof. exact (@lem5335038 term157). Qed.
Lemma lem5335040 : term445 = term293.
Proof. exact (TRANS (@lem5335036) (@lem5335039)). Qed.
Lemma lem5335041 : term293 = term445.
Proof. exact (SYM (@lem5335040)). Qed.
Lemma lem5335042 : term442 = term445.
Proof. exact (TRANS (@lem5335026) (@lem5335041)). Qed.
Lemma lem5335043 : term428 = term352.
Proof. exact (@lem5334993 (@lem5335042)). Qed.
Lemma lem5335044 : term427 = term352.
Proof. exact (TRANS (@lem5334959) (@lem5335043)). Qed.
Lemma lem5335046 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5335047 : term352 = term293.
Proof. exact (@lem5335046 term293). Qed.
Lemma lem5335048 : term427 = term293.
Proof. exact (TRANS (@lem5335044) (@lem5335047)). Qed.
Lemma lem5335049 (_69707 : int) : (term406 _69707) = (term406 _69707).
Proof. exact (eq_refl (term406 _69707)). Qed.
Lemma lem5335050 (_69707 : int) : (term424 _69707) = (term446 _69707).
Proof. exact (MK_COMB (@lem5335049 _69707) (@lem5335048)). Qed.
Lemma lem5335051 (_69707 : int) : (term423 _69707) = (term446 _69707).
Proof. exact (TRANS (@lem5334950 _69707) (@lem5335050 _69707)). Qed.
Lemma lem5335052 (_69707 : int) : (term446 _69707) = (term380 _69707).
Proof. exact (@lem1982723 (term380 _69707)). Qed.
Lemma lem5335053 (_69707 : int) : (term423 _69707) = (term380 _69707).
Proof. exact (TRANS (@lem5335051 _69707) (@lem5335052 _69707)). Qed.
Lemma lem5335054 (_69706 : int) : (term306 _69706) = (term306 _69706).
Proof. exact (eq_refl (term306 _69706)). Qed.
Lemma lem5335055 (_69706 : int) (_69707 : int) : (term422 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (MK_COMB (@lem5335054 _69706) (@lem5335053 _69707)). Qed.
Lemma lem5335056 (_69706 : int) (_69707 : int) : (term421 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (TRANS (@lem5334949 _69706 _69707) (@lem5335055 _69706 _69707)). Qed.
Lemma lem5335057 (_69704 : int) (_69706 : int) (_69707 : int) : (term756 _69704 _69706 _69707) = (term757 _69706 _69707).
Proof. exact (MK_COMB (@lem5334948 _69704) (@lem5335056 _69706 _69707)). Qed.
Lemma lem5335058 (_69704 : int) (_69706 : int) (_69707 : int) : (term755 _69706 _69704 _69707) = (term757 _69706 _69707).
Proof. exact (TRANS (@lem5334840 _69704 _69706 _69707) (@lem5335057 _69704 _69706 _69707)). Qed.
Lemma lem5335059 (_69706 : int) (_69707 : int) : (term757 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (@lem1982721 (term386 _69706 _69707)). Qed.
Lemma lem5335060 (_69704 : int) (_69706 : int) (_69707 : int) : (term755 _69706 _69704 _69707) = (term386 _69706 _69707).
Proof. exact (TRANS (@lem5335058 _69704 _69706 _69707) (@lem5335059 _69706 _69707)). Qed.
Lemma lem5335061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335062 (_69704 : int) (_69706 : int) (_69707 : int) : (term758 _69706 _69704 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5335061) (@lem5335060 _69704 _69706 _69707)). Qed.
Lemma lem5335063 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335064 (_69704 : int) (_69706 : int) (_69707 : int) : (term754 _69706 _69704 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5335062 _69704 _69706 _69707) (@lem5335063)). Qed.
Lemma lem5335065 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term389 _69706 _69707.
Proof. exact (EQ_MP (@lem5335064 _69704 _69706 _69707) (@lem5334839 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335067 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5335068 : term662 = term431.
Proof. exact (@lem5335067 term293 term305). Qed.
Lemma lem5335070 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335071 : term305 = term397.
Proof. exact (@lem5335070 term157). Qed.
Lemma lem5335073 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335074 : term293 = term352.
Proof. exact (@lem5335073 (NUMERAL 0)). Qed.
Lemma lem5335075 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335076 : term663 = term664.
Proof. exact (MK_COMB (@lem5335075) (@lem5335074)). Qed.
Lemma lem5335077 : term431 = term665.
Proof. exact (MK_COMB (@lem5335076) (@lem5335071)). Qed.
Lemma lem5335078 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5335080 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335081 : term431 = term432.
Proof. exact (@lem5335080 (NUMERAL 0) term157). Qed.
Lemma lem5335082 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335083 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335084 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335083 h1) (fun h1 : term432 = True => @lem5335082)). Qed.
Lemma lem5335085 : term432 = True.
Proof. exact (EQ_MP (@lem5335084) (@lem5335082)). Qed.
Lemma lem5335086 : term431 = True.
Proof. exact (TRANS (@lem5335081) (@lem5335085)). Qed.
Lemma lem5335087 : True = term431.
Proof. exact (SYM (@lem5335086)). Qed.
Lemma lem5335088 : term431.
Proof. exact (EQ_MP (@lem5335087) (@lem0)). Qed.
Lemma lem5335089 : term667.
Proof. exact (@lem5335078 (@lem5335088)). Qed.
Lemma lem5335091 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335092 : term431 = term432.
Proof. exact (@lem5335091 (NUMERAL 0) term157). Qed.
Lemma lem5335093 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335094 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335095 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335094 h1) (fun h1 : term432 = True => @lem5335093)). Qed.
Lemma lem5335096 : term432 = True.
Proof. exact (EQ_MP (@lem5335095) (@lem5335093)). Qed.
Lemma lem5335097 : term431 = True.
Proof. exact (TRANS (@lem5335092) (@lem5335096)). Qed.
Lemma lem5335098 : True = term431.
Proof. exact (SYM (@lem5335097)). Qed.
Lemma lem5335099 : term431.
Proof. exact (EQ_MP (@lem5335098) (@lem0)). Qed.
Lemma lem5335100 : term665 = term668.
Proof. exact (@lem5335089 (@lem5335099)). Qed.
Lemma lem5335102 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335103 : term364 = term365.
Proof. exact (@lem5335102 term157 term157). Qed.
Lemma lem5335104 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335105 : term367 = term157.
Proof. exact (EQ_MP (@lem5335104) (@lem940073)). Qed.
Lemma lem5335106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335107 : term365 = term305.
Proof. exact (MK_COMB (@lem5335106) (@lem5335105)). Qed.
Lemma lem5335108 : term364 = term305.
Proof. exact (TRANS (@lem5335103) (@lem5335107)). Qed.
Lemma lem5335110 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335111 : term443 = term293.
Proof. exact (@lem5335110 term157). Qed.
Lemma lem5335112 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335113 : term669 = term663.
Proof. exact (MK_COMB (@lem5335112) (@lem5335111)). Qed.
Lemma lem5335114 : term668 = term431.
Proof. exact (MK_COMB (@lem5335113) (@lem5335108)). Qed.
Lemma lem5335116 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335117 : term431 = term432.
Proof. exact (@lem5335116 (NUMERAL 0) term157). Qed.
Lemma lem5335118 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335119 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335120 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335119 h1) (fun h1 : term432 = True => @lem5335118)). Qed.
Lemma lem5335121 : term432 = True.
Proof. exact (EQ_MP (@lem5335120) (@lem5335118)). Qed.
Lemma lem5335122 : term431 = True.
Proof. exact (TRANS (@lem5335117) (@lem5335121)). Qed.
Lemma lem5335123 : term668 = True.
Proof. exact (TRANS (@lem5335114) (@lem5335122)). Qed.
Lemma lem5335124 : term665 = True.
Proof. exact (TRANS (@lem5335100) (@lem5335123)). Qed.
Lemma lem5335125 : term431 = True.
Proof. exact (TRANS (@lem5335077) (@lem5335124)). Qed.
Lemma lem5335126 : term662 = True.
Proof. exact (TRANS (@lem5335068) (@lem5335125)). Qed.
Lemma lem5335127 : True = term662.
Proof. exact (SYM (@lem5335126)). Qed.
Lemma lem5335128 : term662.
Proof. exact (EQ_MP (@lem5335127) (@lem0)). Qed.
Lemma lem5335129 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term726 _69706 _69707.
Proof. exact (conj (@lem5335128) (@lem5335065 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335131 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5335132 (_69706 : int) (_69707 : int) : term727 _69706 _69707.
Proof. exact (@lem5335131 term305 (term386 _69706 _69707)). Qed.
Lemma lem5335133 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term728 _69706 _69707.
Proof. exact (@lem5335132 _69706 _69707 (@lem5335129 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335134 (_69706 : int) (_69707 : int) : (term729 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (@lem1982733 (term386 _69706 _69707)). Qed.
Lemma lem5335135 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335136 (_69706 : int) (_69707 : int) : (term730 _69706 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5335135) (@lem5335134 _69706 _69707)). Qed.
Lemma lem5335137 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335138 (_69706 : int) (_69707 : int) : (term728 _69706 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5335136 _69706 _69707) (@lem5335137)). Qed.
Lemma lem5335139 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term389 _69706 _69707.
Proof. exact (EQ_MP (@lem5335138 _69706 _69707) (@lem5335133 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335140 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term759 _69706 _69707.
Proof. exact (conj (@lem5335139 _69706 _69705 _69704 _69707 h1) (@lem5334686 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335142 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5335143 (_69706 : int) (_69707 : int) : term760 _69706 _69707.
Proof. exact (@lem5335142 (term386 _69706 _69707) (term412 _69706 _69707)). Qed.
Lemma lem5335144 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term761 _69706 _69707.
Proof. exact (@lem5335143 _69706 _69707 (@lem5335140 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335145 (_69706 : int) (_69707 : int) : (term762 _69706 _69707) = (term763 _69706 _69707).
Proof. exact (@lem1982753 (real_of_int _69706) (term380 _69706) (term380 _69707) (term740 _69707)). Qed.
Lemma lem5335146 (_69706 : int) : (term708 _69706) = (term688 _69706).
Proof. exact (@lem1982715 term355 (real_of_int _69706)). Qed.
Lemma lem5335148 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335149 : term305 = term397.
Proof. exact (@lem5335148 term157). Qed.
Lemma lem5335151 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5335152 : term355 = term356.
Proof. exact (@lem5335151 term157). Qed.
Lemma lem5335153 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335154 : term689 = term690.
Proof. exact (MK_COMB (@lem5335153) (@lem5335152)). Qed.
Lemma lem5335155 : term691 = term692.
Proof. exact (MK_COMB (@lem5335154) (@lem5335149)). Qed.
Lemma lem5335156 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5335158 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335159 : term431 = term432.
Proof. exact (@lem5335158 (NUMERAL 0) term157). Qed.
Lemma lem5335160 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335161 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335162 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335161 h1) (fun h1 : term432 = True => @lem5335160)). Qed.
Lemma lem5335163 : term432 = True.
Proof. exact (EQ_MP (@lem5335162) (@lem5335160)). Qed.
Lemma lem5335164 : term431 = True.
Proof. exact (TRANS (@lem5335159) (@lem5335163)). Qed.
Lemma lem5335165 : True = term431.
Proof. exact (SYM (@lem5335164)). Qed.
Lemma lem5335166 : term431.
Proof. exact (EQ_MP (@lem5335165) (@lem0)). Qed.
Lemma lem5335167 : term694.
Proof. exact (@lem5335156 (@lem5335166)). Qed.
Lemma lem5335169 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335170 : term431 = term432.
Proof. exact (@lem5335169 (NUMERAL 0) term157). Qed.
Lemma lem5335171 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335172 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335173 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335172 h1) (fun h1 : term432 = True => @lem5335171)). Qed.
Lemma lem5335174 : term432 = True.
Proof. exact (EQ_MP (@lem5335173) (@lem5335171)). Qed.
Lemma lem5335175 : term431 = True.
Proof. exact (TRANS (@lem5335170) (@lem5335174)). Qed.
Lemma lem5335176 : True = term431.
Proof. exact (SYM (@lem5335175)). Qed.
Lemma lem5335177 : term431.
Proof. exact (EQ_MP (@lem5335176) (@lem0)). Qed.
Lemma lem5335178 : term695.
Proof. exact (@lem5335167 (@lem5335177)). Qed.
Lemma lem5335180 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335181 : term431 = term432.
Proof. exact (@lem5335180 (NUMERAL 0) term157). Qed.
Lemma lem5335182 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335183 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335184 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335183 h1) (fun h1 : term432 = True => @lem5335182)). Qed.
Lemma lem5335185 : term432 = True.
Proof. exact (EQ_MP (@lem5335184) (@lem5335182)). Qed.
Lemma lem5335186 : term431 = True.
Proof. exact (TRANS (@lem5335181) (@lem5335185)). Qed.
Lemma lem5335187 : True = term431.
Proof. exact (SYM (@lem5335186)). Qed.
Lemma lem5335188 : term431.
Proof. exact (EQ_MP (@lem5335187) (@lem0)). Qed.
Lemma lem5335189 : term696.
Proof. exact (@lem5335178 (@lem5335188)). Qed.
Lemma lem5335191 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335192 : term364 = term365.
Proof. exact (@lem5335191 term157 term157). Qed.
Lemma lem5335193 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335194 : term367 = term157.
Proof. exact (EQ_MP (@lem5335193) (@lem940073)). Qed.
Lemma lem5335195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335196 : term365 = term305.
Proof. exact (MK_COMB (@lem5335195) (@lem5335194)). Qed.
Lemma lem5335197 : term364 = term305.
Proof. exact (TRANS (@lem5335192) (@lem5335196)). Qed.
Lemma lem5335199 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5335200 : term398 = term403.
Proof. exact (@lem5335199 term157 term157). Qed.
Lemma lem5335201 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335202 : term367 = term157.
Proof. exact (EQ_MP (@lem5335201) (@lem940073)). Qed.
Lemma lem5335203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335204 : term365 = term305.
Proof. exact (MK_COMB (@lem5335203) (@lem5335202)). Qed.
Lemma lem5335205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335206 : term403 = term355.
Proof. exact (MK_COMB (@lem5335205) (@lem5335204)). Qed.
Lemma lem5335207 : term398 = term355.
Proof. exact (TRANS (@lem5335200) (@lem5335206)). Qed.
Lemma lem5335208 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335209 : term697 = term689.
Proof. exact (MK_COMB (@lem5335208) (@lem5335207)). Qed.
Lemma lem5335210 : term698 = term691.
Proof. exact (MK_COMB (@lem5335209) (@lem5335197)). Qed.
Lemma lem5335212 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5335213 : term691 = term293.
Proof. exact (@lem5335212 term157). Qed.
Lemma lem5335214 : term698 = term293.
Proof. exact (TRANS (@lem5335210) (@lem5335213)). Qed.
Lemma lem5335215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335216 : term700 = term441.
Proof. exact (MK_COMB (@lem5335215) (@lem5335214)). Qed.
Lemma lem5335217 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5335218 : term701 = term443.
Proof. exact (MK_COMB (@lem5335216) (@lem5335217)). Qed.
Lemma lem5335220 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335221 : term443 = term293.
Proof. exact (@lem5335220 term157). Qed.
Lemma lem5335222 : term701 = term293.
Proof. exact (TRANS (@lem5335218) (@lem5335221)). Qed.
Lemma lem5335224 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335225 : term364 = term365.
Proof. exact (@lem5335224 term157 term157). Qed.
Lemma lem5335226 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335227 : term367 = term157.
Proof. exact (EQ_MP (@lem5335226) (@lem940073)). Qed.
Lemma lem5335228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335229 : term365 = term305.
Proof. exact (MK_COMB (@lem5335228) (@lem5335227)). Qed.
Lemma lem5335230 : term364 = term305.
Proof. exact (TRANS (@lem5335225) (@lem5335229)). Qed.
Lemma lem5335231 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5335232 : term445 = term443.
Proof. exact (MK_COMB (@lem5335231) (@lem5335230)). Qed.
Lemma lem5335234 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335235 : term443 = term293.
Proof. exact (@lem5335234 term157). Qed.
Lemma lem5335236 : term445 = term293.
Proof. exact (TRANS (@lem5335232) (@lem5335235)). Qed.
Lemma lem5335237 : term293 = term445.
Proof. exact (SYM (@lem5335236)). Qed.
Lemma lem5335238 : term701 = term445.
Proof. exact (TRANS (@lem5335222) (@lem5335237)). Qed.
Lemma lem5335239 : term692 = term352.
Proof. exact (@lem5335189 (@lem5335238)). Qed.
Lemma lem5335240 : term691 = term352.
Proof. exact (TRANS (@lem5335155) (@lem5335239)). Qed.
Lemma lem5335242 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5335243 : term352 = term293.
Proof. exact (@lem5335242 term293). Qed.
Lemma lem5335244 : term691 = term293.
Proof. exact (TRANS (@lem5335240) (@lem5335243)). Qed.
Lemma lem5335245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335246 : term702 = term441.
Proof. exact (MK_COMB (@lem5335245) (@lem5335244)). Qed.
Lemma lem5335247 (_69706 : int) : (real_of_int _69706) = (real_of_int _69706).
Proof. exact (eq_refl (real_of_int _69706)). Qed.
Lemma lem5335248 (_69706 : int) : (term688 _69706) = (term703 _69706).
Proof. exact (MK_COMB (@lem5335246) (@lem5335247 _69706)). Qed.
Lemma lem5335249 (_69706 : int) : (term708 _69706) = (term703 _69706).
Proof. exact (TRANS (@lem5335146 _69706) (@lem5335248 _69706)). Qed.
Lemma lem5335250 (_69706 : int) : (term703 _69706) = term293.
Proof. exact (@lem1982719 (real_of_int _69706)). Qed.
Lemma lem5335251 (_69706 : int) : (term708 _69706) = term293.
Proof. exact (TRANS (@lem5335249 _69706) (@lem5335250 _69706)). Qed.
Lemma lem5335252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335253 (_69706 : int) : (term709 _69706) = term705.
Proof. exact (MK_COMB (@lem5335252) (@lem5335251 _69706)). Qed.
Lemma lem5335254 (_69707 : int) : (term764 _69707) = (term765 _69707).
Proof. exact (@lem1982763 (term380 _69707) (real_of_int _69707) term355). Qed.
Lemma lem5335255 (_69707 : int) : (term687 _69707) = (term688 _69707).
Proof. exact (@lem1982713 term355 (real_of_int _69707)). Qed.
Lemma lem5335257 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335258 : term305 = term397.
Proof. exact (@lem5335257 term157). Qed.
Lemma lem5335260 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5335261 : term355 = term356.
Proof. exact (@lem5335260 term157). Qed.
Lemma lem5335262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335263 : term689 = term690.
Proof. exact (MK_COMB (@lem5335262) (@lem5335261)). Qed.
Lemma lem5335264 : term691 = term692.
Proof. exact (MK_COMB (@lem5335263) (@lem5335258)). Qed.
Lemma lem5335265 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5335267 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335268 : term431 = term432.
Proof. exact (@lem5335267 (NUMERAL 0) term157). Qed.
Lemma lem5335269 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335270 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335271 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335270 h1) (fun h1 : term432 = True => @lem5335269)). Qed.
Lemma lem5335272 : term432 = True.
Proof. exact (EQ_MP (@lem5335271) (@lem5335269)). Qed.
Lemma lem5335273 : term431 = True.
Proof. exact (TRANS (@lem5335268) (@lem5335272)). Qed.
Lemma lem5335274 : True = term431.
Proof. exact (SYM (@lem5335273)). Qed.
Lemma lem5335275 : term431.
Proof. exact (EQ_MP (@lem5335274) (@lem0)). Qed.
Lemma lem5335276 : term694.
Proof. exact (@lem5335265 (@lem5335275)). Qed.
Lemma lem5335278 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335279 : term431 = term432.
Proof. exact (@lem5335278 (NUMERAL 0) term157). Qed.
Lemma lem5335280 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335281 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335282 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335281 h1) (fun h1 : term432 = True => @lem5335280)). Qed.
Lemma lem5335283 : term432 = True.
Proof. exact (EQ_MP (@lem5335282) (@lem5335280)). Qed.
Lemma lem5335284 : term431 = True.
Proof. exact (TRANS (@lem5335279) (@lem5335283)). Qed.
Lemma lem5335285 : True = term431.
Proof. exact (SYM (@lem5335284)). Qed.
Lemma lem5335286 : term431.
Proof. exact (EQ_MP (@lem5335285) (@lem0)). Qed.
Lemma lem5335287 : term695.
Proof. exact (@lem5335276 (@lem5335286)). Qed.
Lemma lem5335289 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335290 : term431 = term432.
Proof. exact (@lem5335289 (NUMERAL 0) term157). Qed.
Lemma lem5335291 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335292 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335293 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335292 h1) (fun h1 : term432 = True => @lem5335291)). Qed.
Lemma lem5335294 : term432 = True.
Proof. exact (EQ_MP (@lem5335293) (@lem5335291)). Qed.
Lemma lem5335295 : term431 = True.
Proof. exact (TRANS (@lem5335290) (@lem5335294)). Qed.
Lemma lem5335296 : True = term431.
Proof. exact (SYM (@lem5335295)). Qed.
Lemma lem5335297 : term431.
Proof. exact (EQ_MP (@lem5335296) (@lem0)). Qed.
Lemma lem5335298 : term696.
Proof. exact (@lem5335287 (@lem5335297)). Qed.
Lemma lem5335300 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335301 : term364 = term365.
Proof. exact (@lem5335300 term157 term157). Qed.
Lemma lem5335302 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335303 : term367 = term157.
Proof. exact (EQ_MP (@lem5335302) (@lem940073)). Qed.
Lemma lem5335304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335305 : term365 = term305.
Proof. exact (MK_COMB (@lem5335304) (@lem5335303)). Qed.
Lemma lem5335306 : term364 = term305.
Proof. exact (TRANS (@lem5335301) (@lem5335305)). Qed.
Lemma lem5335308 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5335309 : term398 = term403.
Proof. exact (@lem5335308 term157 term157). Qed.
Lemma lem5335310 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335311 : term367 = term157.
Proof. exact (EQ_MP (@lem5335310) (@lem940073)). Qed.
Lemma lem5335312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335313 : term365 = term305.
Proof. exact (MK_COMB (@lem5335312) (@lem5335311)). Qed.
Lemma lem5335314 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335315 : term403 = term355.
Proof. exact (MK_COMB (@lem5335314) (@lem5335313)). Qed.
Lemma lem5335316 : term398 = term355.
Proof. exact (TRANS (@lem5335309) (@lem5335315)). Qed.
Lemma lem5335317 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335318 : term697 = term689.
Proof. exact (MK_COMB (@lem5335317) (@lem5335316)). Qed.
Lemma lem5335319 : term698 = term691.
Proof. exact (MK_COMB (@lem5335318) (@lem5335306)). Qed.
Lemma lem5335321 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5335322 : term691 = term293.
Proof. exact (@lem5335321 term157). Qed.
Lemma lem5335323 : term698 = term293.
Proof. exact (TRANS (@lem5335319) (@lem5335322)). Qed.
Lemma lem5335324 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335325 : term700 = term441.
Proof. exact (MK_COMB (@lem5335324) (@lem5335323)). Qed.
Lemma lem5335326 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5335327 : term701 = term443.
Proof. exact (MK_COMB (@lem5335325) (@lem5335326)). Qed.
Lemma lem5335329 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335330 : term443 = term293.
Proof. exact (@lem5335329 term157). Qed.
Lemma lem5335331 : term701 = term293.
Proof. exact (TRANS (@lem5335327) (@lem5335330)). Qed.
Lemma lem5335333 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335334 : term364 = term365.
Proof. exact (@lem5335333 term157 term157). Qed.
Lemma lem5335335 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335336 : term367 = term157.
Proof. exact (EQ_MP (@lem5335335) (@lem940073)). Qed.
Lemma lem5335337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335338 : term365 = term305.
Proof. exact (MK_COMB (@lem5335337) (@lem5335336)). Qed.
Lemma lem5335339 : term364 = term305.
Proof. exact (TRANS (@lem5335334) (@lem5335338)). Qed.
Lemma lem5335340 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5335341 : term445 = term443.
Proof. exact (MK_COMB (@lem5335340) (@lem5335339)). Qed.
Lemma lem5335343 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335344 : term443 = term293.
Proof. exact (@lem5335343 term157). Qed.
Lemma lem5335345 : term445 = term293.
Proof. exact (TRANS (@lem5335341) (@lem5335344)). Qed.
Lemma lem5335346 : term293 = term445.
Proof. exact (SYM (@lem5335345)). Qed.
Lemma lem5335347 : term701 = term445.
Proof. exact (TRANS (@lem5335331) (@lem5335346)). Qed.
Lemma lem5335348 : term692 = term352.
Proof. exact (@lem5335298 (@lem5335347)). Qed.
Lemma lem5335349 : term691 = term352.
Proof. exact (TRANS (@lem5335264) (@lem5335348)). Qed.
Lemma lem5335351 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5335352 : term352 = term293.
Proof. exact (@lem5335351 term293). Qed.
Lemma lem5335353 : term691 = term293.
Proof. exact (TRANS (@lem5335349) (@lem5335352)). Qed.
Lemma lem5335354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335355 : term702 = term441.
Proof. exact (MK_COMB (@lem5335354) (@lem5335353)). Qed.
Lemma lem5335356 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5335357 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5335355) (@lem5335356 _69707)). Qed.
Lemma lem5335358 (_69707 : int) : (term687 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5335255 _69707) (@lem5335357 _69707)). Qed.
Lemma lem5335359 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5335360 (_69707 : int) : (term687 _69707) = term293.
Proof. exact (TRANS (@lem5335358 _69707) (@lem5335359 _69707)). Qed.
Lemma lem5335361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335362 (_69707 : int) : (term704 _69707) = term705.
Proof. exact (MK_COMB (@lem5335361) (@lem5335360 _69707)). Qed.
Lemma lem5335363 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5335364 (_69707 : int) : (term765 _69707) = term710.
Proof. exact (MK_COMB (@lem5335362 _69707) (@lem5335363)). Qed.
Lemma lem5335365 (_69707 : int) : (term764 _69707) = term710.
Proof. exact (TRANS (@lem5335254 _69707) (@lem5335364 _69707)). Qed.
Lemma lem5335366 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5335367 (_69707 : int) : (term764 _69707) = term355.
Proof. exact (TRANS (@lem5335365 _69707) (@lem5335366)). Qed.
Lemma lem5335368 (_69706 : int) (_69707 : int) : (term763 _69706 _69707) = term710.
Proof. exact (MK_COMB (@lem5335253 _69706) (@lem5335367 _69707)). Qed.
Lemma lem5335369 (_69706 : int) (_69707 : int) : (term762 _69706 _69707) = term710.
Proof. exact (TRANS (@lem5335145 _69706 _69707) (@lem5335368 _69706 _69707)). Qed.
Lemma lem5335370 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5335371 (_69706 : int) (_69707 : int) : (term762 _69706 _69707) = term355.
Proof. exact (TRANS (@lem5335369 _69706 _69707) (@lem5335370)). Qed.
Lemma lem5335372 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335373 (_69706 : int) (_69707 : int) : (term766 _69706 _69707) = term712.
Proof. exact (MK_COMB (@lem5335372) (@lem5335371 _69706 _69707)). Qed.
Lemma lem5335374 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335375 (_69706 : int) (_69707 : int) : (term761 _69706 _69707) = term713.
Proof. exact (MK_COMB (@lem5335373 _69706 _69707) (@lem5335374)). Qed.
Lemma lem5335376 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : term713.
Proof. exact (EQ_MP (@lem5335375 _69706 _69707) (@lem5335144 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335378 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5335379 : term713 = term714.
Proof. exact (@lem5335378 term293 term355). Qed.
Lemma lem5335381 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5335382 : term355 = term356.
Proof. exact (@lem5335381 term157). Qed.
Lemma lem5335384 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335385 : term293 = term352.
Proof. exact (@lem5335384 (NUMERAL 0)). Qed.
Lemma lem5335386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5335387 : term295 = term715.
Proof. exact (MK_COMB (@lem5335386) (@lem5335385)). Qed.
Lemma lem5335388 : term714 = term716.
Proof. exact (MK_COMB (@lem5335387) (@lem5335382)). Qed.
Lemma lem5335389 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5335391 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335392 : term431 = term432.
Proof. exact (@lem5335391 (NUMERAL 0) term157). Qed.
Lemma lem5335393 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335394 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335395 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335394 h1) (fun h1 : term432 = True => @lem5335393)). Qed.
Lemma lem5335396 : term432 = True.
Proof. exact (EQ_MP (@lem5335395) (@lem5335393)). Qed.
Lemma lem5335397 : term431 = True.
Proof. exact (TRANS (@lem5335392) (@lem5335396)). Qed.
Lemma lem5335398 : True = term431.
Proof. exact (SYM (@lem5335397)). Qed.
Lemma lem5335399 : term431.
Proof. exact (EQ_MP (@lem5335398) (@lem0)). Qed.
Lemma lem5335400 : term718.
Proof. exact (@lem5335389 (@lem5335399)). Qed.
Lemma lem5335402 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335403 : term431 = term432.
Proof. exact (@lem5335402 (NUMERAL 0) term157). Qed.
Lemma lem5335404 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335405 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335406 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335405 h1) (fun h1 : term432 = True => @lem5335404)). Qed.
Lemma lem5335407 : term432 = True.
Proof. exact (EQ_MP (@lem5335406) (@lem5335404)). Qed.
Lemma lem5335408 : term431 = True.
Proof. exact (TRANS (@lem5335403) (@lem5335407)). Qed.
Lemma lem5335409 : True = term431.
Proof. exact (SYM (@lem5335408)). Qed.
Lemma lem5335410 : term431.
Proof. exact (EQ_MP (@lem5335409) (@lem0)). Qed.
Lemma lem5335411 : term716 = term719.
Proof. exact (@lem5335400 (@lem5335410)). Qed.
Lemma lem5335413 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5335414 : term398 = term403.
Proof. exact (@lem5335413 term157 term157). Qed.
Lemma lem5335415 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335416 : term367 = term157.
Proof. exact (EQ_MP (@lem5335415) (@lem940073)). Qed.
Lemma lem5335417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335418 : term365 = term305.
Proof. exact (MK_COMB (@lem5335417) (@lem5335416)). Qed.
Lemma lem5335419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335420 : term403 = term355.
Proof. exact (MK_COMB (@lem5335419) (@lem5335418)). Qed.
Lemma lem5335421 : term398 = term355.
Proof. exact (TRANS (@lem5335414) (@lem5335420)). Qed.
Lemma lem5335423 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335424 : term443 = term293.
Proof. exact (@lem5335423 term157). Qed.
Lemma lem5335425 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5335426 : term720 = term295.
Proof. exact (MK_COMB (@lem5335425) (@lem5335424)). Qed.
Lemma lem5335427 : term719 = term714.
Proof. exact (MK_COMB (@lem5335426) (@lem5335421)). Qed.
Lemma lem5335429 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5335430 : term714 = term723.
Proof. exact (@lem5335429 (NUMERAL 0) term157). Qed.
Lemma lem5335431 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335432 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5335433 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335432 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5335431)). Qed.
Lemma lem5335434 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5335433) (@lem5335431)). Qed.
Lemma lem5335435 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5335436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5335437 : term724 = (and True).
Proof. exact (MK_COMB (@lem5335436) (@lem5335435)). Qed.
Lemma lem5335438 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5335437) (@lem5335434)). Qed.
Lemma lem5335440 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5335441 : term723 = False.
Proof. exact (TRANS (@lem5335438) (@lem5335440)). Qed.
Lemma lem5335442 : term714 = False.
Proof. exact (TRANS (@lem5335430) (@lem5335441)). Qed.
Lemma lem5335443 : term719 = False.
Proof. exact (TRANS (@lem5335427) (@lem5335442)). Qed.
Lemma lem5335444 : term716 = False.
Proof. exact (TRANS (@lem5335411) (@lem5335443)). Qed.
Lemma lem5335445 : term714 = False.
Proof. exact (TRANS (@lem5335388) (@lem5335444)). Qed.
Lemma lem5335446 : term713 = False.
Proof. exact (TRANS (@lem5335379) (@lem5335445)). Qed.
Lemma lem5335447 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term746 _69706 _69705 _69704 _69707) : False.
Proof. exact (EQ_MP (@lem5335446) (@lem5335376 _69706 _69705 _69704 _69707 h1)). Qed.
Lemma lem5335448 (_69706 : int) (_69705 : int) (_69704 : int) (_69707 : int) (h1 : term639 _69706 _69705 _69704 _69707) : False.
Proof. exact (or_elim (@lem5334122 _69706 _69705 _69704 _69707 h1) (fun h0 : term745 _69705 _69706 _69704 _69707 => @lem5334595 _69705 _69706 _69704 _69707 h0) (fun h0 : term746 _69706 _69705 _69704 _69707 => @lem5335447 _69706 _69705 _69704 _69707 h0)). Qed.
Lemma lem5335449 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term635 _69704 _69706 _69705 _69707) : term635 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5335450 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term767 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5335451 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term636 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5335450 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335453 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term605 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5335451 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335455 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term574 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5335453 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335457 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term543 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5335455 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335459 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term512 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5335457 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335460 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term391 _69704 _69705 _69706.
Proof. exact (proj1 (@lem5335457 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335461 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term389 _69705 _69706.
Proof. exact (proj2 (@lem5335460 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335463 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term414 _69705 _69707.
Proof. exact (proj2 (@lem5335459 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335464 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term456 _69704 _69706 _69707.
Proof. exact (proj1 (@lem5335459 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335465 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term389 _69706 _69707.
Proof. exact (proj2 (@lem5335464 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335468 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5335469 : term662 = term431.
Proof. exact (@lem5335468 term293 term305). Qed.
Lemma lem5335471 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335472 : term305 = term397.
Proof. exact (@lem5335471 term157). Qed.
Lemma lem5335474 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335475 : term293 = term352.
Proof. exact (@lem5335474 (NUMERAL 0)). Qed.
Lemma lem5335476 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335477 : term663 = term664.
Proof. exact (MK_COMB (@lem5335476) (@lem5335475)). Qed.
Lemma lem5335478 : term431 = term665.
Proof. exact (MK_COMB (@lem5335477) (@lem5335472)). Qed.
Lemma lem5335479 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5335481 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335482 : term431 = term432.
Proof. exact (@lem5335481 (NUMERAL 0) term157). Qed.
Lemma lem5335483 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335484 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335485 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335484 h1) (fun h1 : term432 = True => @lem5335483)). Qed.
Lemma lem5335486 : term432 = True.
Proof. exact (EQ_MP (@lem5335485) (@lem5335483)). Qed.
Lemma lem5335487 : term431 = True.
Proof. exact (TRANS (@lem5335482) (@lem5335486)). Qed.
Lemma lem5335488 : True = term431.
Proof. exact (SYM (@lem5335487)). Qed.
Lemma lem5335489 : term431.
Proof. exact (EQ_MP (@lem5335488) (@lem0)). Qed.
Lemma lem5335490 : term667.
Proof. exact (@lem5335479 (@lem5335489)). Qed.
Lemma lem5335492 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335493 : term431 = term432.
Proof. exact (@lem5335492 (NUMERAL 0) term157). Qed.
Lemma lem5335494 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335495 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335496 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335495 h1) (fun h1 : term432 = True => @lem5335494)). Qed.
Lemma lem5335497 : term432 = True.
Proof. exact (EQ_MP (@lem5335496) (@lem5335494)). Qed.
Lemma lem5335498 : term431 = True.
Proof. exact (TRANS (@lem5335493) (@lem5335497)). Qed.
Lemma lem5335499 : True = term431.
Proof. exact (SYM (@lem5335498)). Qed.
Lemma lem5335500 : term431.
Proof. exact (EQ_MP (@lem5335499) (@lem0)). Qed.
Lemma lem5335501 : term665 = term668.
Proof. exact (@lem5335490 (@lem5335500)). Qed.
Lemma lem5335503 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335504 : term364 = term365.
Proof. exact (@lem5335503 term157 term157). Qed.
Lemma lem5335505 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335506 : term367 = term157.
Proof. exact (EQ_MP (@lem5335505) (@lem940073)). Qed.
Lemma lem5335507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335508 : term365 = term305.
Proof. exact (MK_COMB (@lem5335507) (@lem5335506)). Qed.
Lemma lem5335509 : term364 = term305.
Proof. exact (TRANS (@lem5335504) (@lem5335508)). Qed.
Lemma lem5335511 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335512 : term443 = term293.
Proof. exact (@lem5335511 term157). Qed.
Lemma lem5335513 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335514 : term669 = term663.
Proof. exact (MK_COMB (@lem5335513) (@lem5335512)). Qed.
Lemma lem5335515 : term668 = term431.
Proof. exact (MK_COMB (@lem5335514) (@lem5335509)). Qed.
Lemma lem5335517 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335518 : term431 = term432.
Proof. exact (@lem5335517 (NUMERAL 0) term157). Qed.
Lemma lem5335519 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335520 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335521 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335520 h1) (fun h1 : term432 = True => @lem5335519)). Qed.
Lemma lem5335522 : term432 = True.
Proof. exact (EQ_MP (@lem5335521) (@lem5335519)). Qed.
Lemma lem5335523 : term431 = True.
Proof. exact (TRANS (@lem5335518) (@lem5335522)). Qed.
Lemma lem5335524 : term668 = True.
Proof. exact (TRANS (@lem5335515) (@lem5335523)). Qed.
Lemma lem5335525 : term665 = True.
Proof. exact (TRANS (@lem5335501) (@lem5335524)). Qed.
Lemma lem5335526 : term431 = True.
Proof. exact (TRANS (@lem5335478) (@lem5335525)). Qed.
Lemma lem5335527 : term662 = True.
Proof. exact (TRANS (@lem5335469) (@lem5335526)). Qed.
Lemma lem5335528 : True = term662.
Proof. exact (SYM (@lem5335527)). Qed.
Lemma lem5335529 : term662.
Proof. exact (EQ_MP (@lem5335528) (@lem0)). Qed.
Lemma lem5335530 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term726 _69706 _69707.
Proof. exact (conj (@lem5335529) (@lem5335465 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335532 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5335533 (_69706 : int) (_69707 : int) : term727 _69706 _69707.
Proof. exact (@lem5335532 term305 (term386 _69706 _69707)). Qed.
Lemma lem5335534 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term728 _69706 _69707.
Proof. exact (@lem5335533 _69706 _69707 (@lem5335530 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335535 (_69706 : int) (_69707 : int) : (term729 _69706 _69707) = (term386 _69706 _69707).
Proof. exact (@lem1982733 (term386 _69706 _69707)). Qed.
Lemma lem5335536 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335537 (_69706 : int) (_69707 : int) : (term730 _69706 _69707) = (term388 _69706 _69707).
Proof. exact (MK_COMB (@lem5335536) (@lem5335535 _69706 _69707)). Qed.
Lemma lem5335538 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335539 (_69706 : int) (_69707 : int) : (term728 _69706 _69707) = (term389 _69706 _69707).
Proof. exact (MK_COMB (@lem5335537 _69706 _69707) (@lem5335538)). Qed.
Lemma lem5335540 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term389 _69706 _69707.
Proof. exact (EQ_MP (@lem5335539 _69706 _69707) (@lem5335534 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335542 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5335543 : term662 = term431.
Proof. exact (@lem5335542 term293 term305). Qed.
Lemma lem5335545 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335546 : term305 = term397.
Proof. exact (@lem5335545 term157). Qed.
Lemma lem5335548 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335549 : term293 = term352.
Proof. exact (@lem5335548 (NUMERAL 0)). Qed.
Lemma lem5335550 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335551 : term663 = term664.
Proof. exact (MK_COMB (@lem5335550) (@lem5335549)). Qed.
Lemma lem5335552 : term431 = term665.
Proof. exact (MK_COMB (@lem5335551) (@lem5335546)). Qed.
Lemma lem5335553 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5335555 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335556 : term431 = term432.
Proof. exact (@lem5335555 (NUMERAL 0) term157). Qed.
Lemma lem5335557 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335558 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335559 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335558 h1) (fun h1 : term432 = True => @lem5335557)). Qed.
Lemma lem5335560 : term432 = True.
Proof. exact (EQ_MP (@lem5335559) (@lem5335557)). Qed.
Lemma lem5335561 : term431 = True.
Proof. exact (TRANS (@lem5335556) (@lem5335560)). Qed.
Lemma lem5335562 : True = term431.
Proof. exact (SYM (@lem5335561)). Qed.
Lemma lem5335563 : term431.
Proof. exact (EQ_MP (@lem5335562) (@lem0)). Qed.
Lemma lem5335564 : term667.
Proof. exact (@lem5335553 (@lem5335563)). Qed.
Lemma lem5335566 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335567 : term431 = term432.
Proof. exact (@lem5335566 (NUMERAL 0) term157). Qed.
Lemma lem5335568 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335569 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335570 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335569 h1) (fun h1 : term432 = True => @lem5335568)). Qed.
Lemma lem5335571 : term432 = True.
Proof. exact (EQ_MP (@lem5335570) (@lem5335568)). Qed.
Lemma lem5335572 : term431 = True.
Proof. exact (TRANS (@lem5335567) (@lem5335571)). Qed.
Lemma lem5335573 : True = term431.
Proof. exact (SYM (@lem5335572)). Qed.
Lemma lem5335574 : term431.
Proof. exact (EQ_MP (@lem5335573) (@lem0)). Qed.
Lemma lem5335575 : term665 = term668.
Proof. exact (@lem5335564 (@lem5335574)). Qed.
Lemma lem5335577 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335578 : term364 = term365.
Proof. exact (@lem5335577 term157 term157). Qed.
Lemma lem5335579 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335580 : term367 = term157.
Proof. exact (EQ_MP (@lem5335579) (@lem940073)). Qed.
Lemma lem5335581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335582 : term365 = term305.
Proof. exact (MK_COMB (@lem5335581) (@lem5335580)). Qed.
Lemma lem5335583 : term364 = term305.
Proof. exact (TRANS (@lem5335578) (@lem5335582)). Qed.
Lemma lem5335585 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335586 : term443 = term293.
Proof. exact (@lem5335585 term157). Qed.
Lemma lem5335587 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335588 : term669 = term663.
Proof. exact (MK_COMB (@lem5335587) (@lem5335586)). Qed.
Lemma lem5335589 : term668 = term431.
Proof. exact (MK_COMB (@lem5335588) (@lem5335583)). Qed.
Lemma lem5335591 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335592 : term431 = term432.
Proof. exact (@lem5335591 (NUMERAL 0) term157). Qed.
Lemma lem5335593 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335594 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335595 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335594 h1) (fun h1 : term432 = True => @lem5335593)). Qed.
Lemma lem5335596 : term432 = True.
Proof. exact (EQ_MP (@lem5335595) (@lem5335593)). Qed.
Lemma lem5335597 : term431 = True.
Proof. exact (TRANS (@lem5335592) (@lem5335596)). Qed.
Lemma lem5335598 : term668 = True.
Proof. exact (TRANS (@lem5335589) (@lem5335597)). Qed.
Lemma lem5335599 : term665 = True.
Proof. exact (TRANS (@lem5335575) (@lem5335598)). Qed.
Lemma lem5335600 : term431 = True.
Proof. exact (TRANS (@lem5335552) (@lem5335599)). Qed.
Lemma lem5335601 : term662 = True.
Proof. exact (TRANS (@lem5335543) (@lem5335600)). Qed.
Lemma lem5335602 : True = term662.
Proof. exact (SYM (@lem5335601)). Qed.
Lemma lem5335603 : term662.
Proof. exact (EQ_MP (@lem5335602) (@lem0)). Qed.
Lemma lem5335604 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term726 _69705 _69706.
Proof. exact (conj (@lem5335603) (@lem5335461 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335606 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5335607 (_69705 : int) (_69706 : int) : term727 _69705 _69706.
Proof. exact (@lem5335606 term305 (term386 _69705 _69706)). Qed.
Lemma lem5335608 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term728 _69705 _69706.
Proof. exact (@lem5335607 _69705 _69706 (@lem5335604 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335609 (_69705 : int) (_69706 : int) : (term729 _69705 _69706) = (term386 _69705 _69706).
Proof. exact (@lem1982733 (term386 _69705 _69706)). Qed.
Lemma lem5335610 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335611 (_69705 : int) (_69706 : int) : (term730 _69705 _69706) = (term388 _69705 _69706).
Proof. exact (MK_COMB (@lem5335610) (@lem5335609 _69705 _69706)). Qed.
Lemma lem5335612 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335613 (_69705 : int) (_69706 : int) : (term728 _69705 _69706) = (term389 _69705 _69706).
Proof. exact (MK_COMB (@lem5335611 _69705 _69706) (@lem5335612)). Qed.
Lemma lem5335614 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term389 _69705 _69706.
Proof. exact (EQ_MP (@lem5335613 _69705 _69706) (@lem5335608 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335616 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5335617 : term662 = term431.
Proof. exact (@lem5335616 term293 term305). Qed.
Lemma lem5335619 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335620 : term305 = term397.
Proof. exact (@lem5335619 term157). Qed.
Lemma lem5335622 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335623 : term293 = term352.
Proof. exact (@lem5335622 (NUMERAL 0)). Qed.
Lemma lem5335624 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335625 : term663 = term664.
Proof. exact (MK_COMB (@lem5335624) (@lem5335623)). Qed.
Lemma lem5335626 : term431 = term665.
Proof. exact (MK_COMB (@lem5335625) (@lem5335620)). Qed.
Lemma lem5335627 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5335629 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335630 : term431 = term432.
Proof. exact (@lem5335629 (NUMERAL 0) term157). Qed.
Lemma lem5335631 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335632 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335633 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335632 h1) (fun h1 : term432 = True => @lem5335631)). Qed.
Lemma lem5335634 : term432 = True.
Proof. exact (EQ_MP (@lem5335633) (@lem5335631)). Qed.
Lemma lem5335635 : term431 = True.
Proof. exact (TRANS (@lem5335630) (@lem5335634)). Qed.
Lemma lem5335636 : True = term431.
Proof. exact (SYM (@lem5335635)). Qed.
Lemma lem5335637 : term431.
Proof. exact (EQ_MP (@lem5335636) (@lem0)). Qed.
Lemma lem5335638 : term667.
Proof. exact (@lem5335627 (@lem5335637)). Qed.
Lemma lem5335640 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335641 : term431 = term432.
Proof. exact (@lem5335640 (NUMERAL 0) term157). Qed.
Lemma lem5335642 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335643 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335644 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335643 h1) (fun h1 : term432 = True => @lem5335642)). Qed.
Lemma lem5335645 : term432 = True.
Proof. exact (EQ_MP (@lem5335644) (@lem5335642)). Qed.
Lemma lem5335646 : term431 = True.
Proof. exact (TRANS (@lem5335641) (@lem5335645)). Qed.
Lemma lem5335647 : True = term431.
Proof. exact (SYM (@lem5335646)). Qed.
Lemma lem5335648 : term431.
Proof. exact (EQ_MP (@lem5335647) (@lem0)). Qed.
Lemma lem5335649 : term665 = term668.
Proof. exact (@lem5335638 (@lem5335648)). Qed.
Lemma lem5335651 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335652 : term364 = term365.
Proof. exact (@lem5335651 term157 term157). Qed.
Lemma lem5335653 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335654 : term367 = term157.
Proof. exact (EQ_MP (@lem5335653) (@lem940073)). Qed.
Lemma lem5335655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335656 : term365 = term305.
Proof. exact (MK_COMB (@lem5335655) (@lem5335654)). Qed.
Lemma lem5335657 : term364 = term305.
Proof. exact (TRANS (@lem5335652) (@lem5335656)). Qed.
Lemma lem5335659 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335660 : term443 = term293.
Proof. exact (@lem5335659 term157). Qed.
Lemma lem5335661 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335662 : term669 = term663.
Proof. exact (MK_COMB (@lem5335661) (@lem5335660)). Qed.
Lemma lem5335663 : term668 = term431.
Proof. exact (MK_COMB (@lem5335662) (@lem5335657)). Qed.
Lemma lem5335665 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335666 : term431 = term432.
Proof. exact (@lem5335665 (NUMERAL 0) term157). Qed.
Lemma lem5335667 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335668 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335669 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335668 h1) (fun h1 : term432 = True => @lem5335667)). Qed.
Lemma lem5335670 : term432 = True.
Proof. exact (EQ_MP (@lem5335669) (@lem5335667)). Qed.
Lemma lem5335671 : term431 = True.
Proof. exact (TRANS (@lem5335666) (@lem5335670)). Qed.
Lemma lem5335672 : term668 = True.
Proof. exact (TRANS (@lem5335663) (@lem5335671)). Qed.
Lemma lem5335673 : term665 = True.
Proof. exact (TRANS (@lem5335649) (@lem5335672)). Qed.
Lemma lem5335674 : term431 = True.
Proof. exact (TRANS (@lem5335626) (@lem5335673)). Qed.
Lemma lem5335675 : term662 = True.
Proof. exact (TRANS (@lem5335617) (@lem5335674)). Qed.
Lemma lem5335676 : True = term662.
Proof. exact (SYM (@lem5335675)). Qed.
Lemma lem5335677 : term662.
Proof. exact (EQ_MP (@lem5335676) (@lem0)). Qed.
Lemma lem5335678 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term731 _69705 _69707.
Proof. exact (conj (@lem5335677) (@lem5335463 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335680 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5335681 (_69705 : int) (_69707 : int) : term732 _69705 _69707.
Proof. exact (@lem5335680 term305 (term412 _69705 _69707)). Qed.
Lemma lem5335682 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term733 _69705 _69707.
Proof. exact (@lem5335681 _69705 _69707 (@lem5335678 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335683 (_69705 : int) (_69707 : int) : (term734 _69705 _69707) = (term412 _69705 _69707).
Proof. exact (@lem1982733 (term412 _69705 _69707)). Qed.
Lemma lem5335684 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335685 (_69705 : int) (_69707 : int) : (term735 _69705 _69707) = (term413 _69705 _69707).
Proof. exact (MK_COMB (@lem5335684) (@lem5335683 _69705 _69707)). Qed.
Lemma lem5335686 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335687 (_69705 : int) (_69707 : int) : (term733 _69705 _69707) = (term414 _69705 _69707).
Proof. exact (MK_COMB (@lem5335685 _69705 _69707) (@lem5335686)). Qed.
Lemma lem5335688 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term414 _69705 _69707.
Proof. exact (EQ_MP (@lem5335687 _69705 _69707) (@lem5335682 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335689 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term768 _69707 _69705 _69706.
Proof. exact (conj (@lem5335688 _69704 _69706 _69705 _69707 h1) (@lem5335614 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335691 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5335692 (_69707 : int) (_69705 : int) (_69706 : int) : term769 _69707 _69705 _69706.
Proof. exact (@lem5335691 (term412 _69705 _69707) (term386 _69705 _69706)). Qed.
Lemma lem5335693 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term770 _69707 _69705 _69706.
Proof. exact (@lem5335692 _69707 _69705 _69706 (@lem5335689 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335694 (_69705 : int) (_69707 : int) (_69706 : int) : (term771 _69707 _69705 _69706) = (term772 _69705 _69707 _69706).
Proof. exact (@lem1982753 (term380 _69705) (real_of_int _69705) (term740 _69707) (term380 _69706)). Qed.
Lemma lem5335695 (_69705 : int) : (term687 _69705) = (term688 _69705).
Proof. exact (@lem1982713 term355 (real_of_int _69705)). Qed.
Lemma lem5335697 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335698 : term305 = term397.
Proof. exact (@lem5335697 term157). Qed.
Lemma lem5335700 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5335701 : term355 = term356.
Proof. exact (@lem5335700 term157). Qed.
Lemma lem5335702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335703 : term689 = term690.
Proof. exact (MK_COMB (@lem5335702) (@lem5335701)). Qed.
Lemma lem5335704 : term691 = term692.
Proof. exact (MK_COMB (@lem5335703) (@lem5335698)). Qed.
Lemma lem5335705 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5335707 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335708 : term431 = term432.
Proof. exact (@lem5335707 (NUMERAL 0) term157). Qed.
Lemma lem5335709 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335710 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335711 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335710 h1) (fun h1 : term432 = True => @lem5335709)). Qed.
Lemma lem5335712 : term432 = True.
Proof. exact (EQ_MP (@lem5335711) (@lem5335709)). Qed.
Lemma lem5335713 : term431 = True.
Proof. exact (TRANS (@lem5335708) (@lem5335712)). Qed.
Lemma lem5335714 : True = term431.
Proof. exact (SYM (@lem5335713)). Qed.
Lemma lem5335715 : term431.
Proof. exact (EQ_MP (@lem5335714) (@lem0)). Qed.
Lemma lem5335716 : term694.
Proof. exact (@lem5335705 (@lem5335715)). Qed.
Lemma lem5335718 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335719 : term431 = term432.
Proof. exact (@lem5335718 (NUMERAL 0) term157). Qed.
Lemma lem5335720 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335721 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335722 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335721 h1) (fun h1 : term432 = True => @lem5335720)). Qed.
Lemma lem5335723 : term432 = True.
Proof. exact (EQ_MP (@lem5335722) (@lem5335720)). Qed.
Lemma lem5335724 : term431 = True.
Proof. exact (TRANS (@lem5335719) (@lem5335723)). Qed.
Lemma lem5335725 : True = term431.
Proof. exact (SYM (@lem5335724)). Qed.
Lemma lem5335726 : term431.
Proof. exact (EQ_MP (@lem5335725) (@lem0)). Qed.
Lemma lem5335727 : term695.
Proof. exact (@lem5335716 (@lem5335726)). Qed.
Lemma lem5335729 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335730 : term431 = term432.
Proof. exact (@lem5335729 (NUMERAL 0) term157). Qed.
Lemma lem5335731 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335732 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335733 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335732 h1) (fun h1 : term432 = True => @lem5335731)). Qed.
Lemma lem5335734 : term432 = True.
Proof. exact (EQ_MP (@lem5335733) (@lem5335731)). Qed.
Lemma lem5335735 : term431 = True.
Proof. exact (TRANS (@lem5335730) (@lem5335734)). Qed.
Lemma lem5335736 : True = term431.
Proof. exact (SYM (@lem5335735)). Qed.
Lemma lem5335737 : term431.
Proof. exact (EQ_MP (@lem5335736) (@lem0)). Qed.
Lemma lem5335738 : term696.
Proof. exact (@lem5335727 (@lem5335737)). Qed.
Lemma lem5335740 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335741 : term364 = term365.
Proof. exact (@lem5335740 term157 term157). Qed.
Lemma lem5335742 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335743 : term367 = term157.
Proof. exact (EQ_MP (@lem5335742) (@lem940073)). Qed.
Lemma lem5335744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335745 : term365 = term305.
Proof. exact (MK_COMB (@lem5335744) (@lem5335743)). Qed.
Lemma lem5335746 : term364 = term305.
Proof. exact (TRANS (@lem5335741) (@lem5335745)). Qed.
Lemma lem5335748 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5335749 : term398 = term403.
Proof. exact (@lem5335748 term157 term157). Qed.
Lemma lem5335750 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335751 : term367 = term157.
Proof. exact (EQ_MP (@lem5335750) (@lem940073)). Qed.
Lemma lem5335752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335753 : term365 = term305.
Proof. exact (MK_COMB (@lem5335752) (@lem5335751)). Qed.
Lemma lem5335754 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335755 : term403 = term355.
Proof. exact (MK_COMB (@lem5335754) (@lem5335753)). Qed.
Lemma lem5335756 : term398 = term355.
Proof. exact (TRANS (@lem5335749) (@lem5335755)). Qed.
Lemma lem5335757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335758 : term697 = term689.
Proof. exact (MK_COMB (@lem5335757) (@lem5335756)). Qed.
Lemma lem5335759 : term698 = term691.
Proof. exact (MK_COMB (@lem5335758) (@lem5335746)). Qed.
Lemma lem5335761 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5335762 : term691 = term293.
Proof. exact (@lem5335761 term157). Qed.
Lemma lem5335763 : term698 = term293.
Proof. exact (TRANS (@lem5335759) (@lem5335762)). Qed.
Lemma lem5335764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335765 : term700 = term441.
Proof. exact (MK_COMB (@lem5335764) (@lem5335763)). Qed.
Lemma lem5335766 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5335767 : term701 = term443.
Proof. exact (MK_COMB (@lem5335765) (@lem5335766)). Qed.
Lemma lem5335769 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335770 : term443 = term293.
Proof. exact (@lem5335769 term157). Qed.
Lemma lem5335771 : term701 = term293.
Proof. exact (TRANS (@lem5335767) (@lem5335770)). Qed.
Lemma lem5335773 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335774 : term364 = term365.
Proof. exact (@lem5335773 term157 term157). Qed.
Lemma lem5335775 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335776 : term367 = term157.
Proof. exact (EQ_MP (@lem5335775) (@lem940073)). Qed.
Lemma lem5335777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335778 : term365 = term305.
Proof. exact (MK_COMB (@lem5335777) (@lem5335776)). Qed.
Lemma lem5335779 : term364 = term305.
Proof. exact (TRANS (@lem5335774) (@lem5335778)). Qed.
Lemma lem5335780 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5335781 : term445 = term443.
Proof. exact (MK_COMB (@lem5335780) (@lem5335779)). Qed.
Lemma lem5335783 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335784 : term443 = term293.
Proof. exact (@lem5335783 term157). Qed.
Lemma lem5335785 : term445 = term293.
Proof. exact (TRANS (@lem5335781) (@lem5335784)). Qed.
Lemma lem5335786 : term293 = term445.
Proof. exact (SYM (@lem5335785)). Qed.
Lemma lem5335787 : term701 = term445.
Proof. exact (TRANS (@lem5335771) (@lem5335786)). Qed.
Lemma lem5335788 : term692 = term352.
Proof. exact (@lem5335738 (@lem5335787)). Qed.
Lemma lem5335789 : term691 = term352.
Proof. exact (TRANS (@lem5335704) (@lem5335788)). Qed.
Lemma lem5335791 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5335792 : term352 = term293.
Proof. exact (@lem5335791 term293). Qed.
Lemma lem5335793 : term691 = term293.
Proof. exact (TRANS (@lem5335789) (@lem5335792)). Qed.
Lemma lem5335794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335795 : term702 = term441.
Proof. exact (MK_COMB (@lem5335794) (@lem5335793)). Qed.
Lemma lem5335796 (_69705 : int) : (real_of_int _69705) = (real_of_int _69705).
Proof. exact (eq_refl (real_of_int _69705)). Qed.
Lemma lem5335797 (_69705 : int) : (term688 _69705) = (term703 _69705).
Proof. exact (MK_COMB (@lem5335795) (@lem5335796 _69705)). Qed.
Lemma lem5335798 (_69705 : int) : (term687 _69705) = (term703 _69705).
Proof. exact (TRANS (@lem5335695 _69705) (@lem5335797 _69705)). Qed.
Lemma lem5335799 (_69705 : int) : (term703 _69705) = term293.
Proof. exact (@lem1982719 (real_of_int _69705)). Qed.
Lemma lem5335800 (_69705 : int) : (term687 _69705) = term293.
Proof. exact (TRANS (@lem5335798 _69705) (@lem5335799 _69705)). Qed.
Lemma lem5335801 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335802 (_69705 : int) : (term704 _69705) = term705.
Proof. exact (MK_COMB (@lem5335801) (@lem5335800 _69705)). Qed.
Lemma lem5335803 (_69706 : int) (_69707 : int) : (term773 _69707 _69706) = (term412 _69706 _69707).
Proof. exact (@lem1982761 (term380 _69706) (term740 _69707)). Qed.
Lemma lem5335804 (_69705 : int) (_69706 : int) (_69707 : int) : (term772 _69705 _69707 _69706) = (term774 _69706 _69707).
Proof. exact (MK_COMB (@lem5335802 _69705) (@lem5335803 _69706 _69707)). Qed.
Lemma lem5335805 (_69705 : int) (_69706 : int) (_69707 : int) : (term771 _69707 _69705 _69706) = (term774 _69706 _69707).
Proof. exact (TRANS (@lem5335694 _69705 _69707 _69706) (@lem5335804 _69705 _69706 _69707)). Qed.
Lemma lem5335806 (_69706 : int) (_69707 : int) : (term774 _69706 _69707) = (term412 _69706 _69707).
Proof. exact (@lem1982721 (term412 _69706 _69707)). Qed.
Lemma lem5335807 (_69705 : int) (_69706 : int) (_69707 : int) : (term771 _69707 _69705 _69706) = (term412 _69706 _69707).
Proof. exact (TRANS (@lem5335805 _69705 _69706 _69707) (@lem5335806 _69706 _69707)). Qed.
Lemma lem5335808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335809 (_69705 : int) (_69706 : int) (_69707 : int) : (term775 _69707 _69705 _69706) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5335808) (@lem5335807 _69705 _69706 _69707)). Qed.
Lemma lem5335810 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335811 (_69705 : int) (_69706 : int) (_69707 : int) : (term770 _69707 _69705 _69706) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5335809 _69705 _69706 _69707) (@lem5335810)). Qed.
Lemma lem5335812 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term414 _69706 _69707.
Proof. exact (EQ_MP (@lem5335811 _69705 _69706 _69707) (@lem5335693 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335814 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5335815 : term662 = term431.
Proof. exact (@lem5335814 term293 term305). Qed.
Lemma lem5335817 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335818 : term305 = term397.
Proof. exact (@lem5335817 term157). Qed.
Lemma lem5335820 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335821 : term293 = term352.
Proof. exact (@lem5335820 (NUMERAL 0)). Qed.
Lemma lem5335822 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335823 : term663 = term664.
Proof. exact (MK_COMB (@lem5335822) (@lem5335821)). Qed.
Lemma lem5335824 : term431 = term665.
Proof. exact (MK_COMB (@lem5335823) (@lem5335818)). Qed.
Lemma lem5335825 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5335827 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335828 : term431 = term432.
Proof. exact (@lem5335827 (NUMERAL 0) term157). Qed.
Lemma lem5335829 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335830 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335831 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335830 h1) (fun h1 : term432 = True => @lem5335829)). Qed.
Lemma lem5335832 : term432 = True.
Proof. exact (EQ_MP (@lem5335831) (@lem5335829)). Qed.
Lemma lem5335833 : term431 = True.
Proof. exact (TRANS (@lem5335828) (@lem5335832)). Qed.
Lemma lem5335834 : True = term431.
Proof. exact (SYM (@lem5335833)). Qed.
Lemma lem5335835 : term431.
Proof. exact (EQ_MP (@lem5335834) (@lem0)). Qed.
Lemma lem5335836 : term667.
Proof. exact (@lem5335825 (@lem5335835)). Qed.
Lemma lem5335838 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335839 : term431 = term432.
Proof. exact (@lem5335838 (NUMERAL 0) term157). Qed.
Lemma lem5335840 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335841 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335842 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335841 h1) (fun h1 : term432 = True => @lem5335840)). Qed.
Lemma lem5335843 : term432 = True.
Proof. exact (EQ_MP (@lem5335842) (@lem5335840)). Qed.
Lemma lem5335844 : term431 = True.
Proof. exact (TRANS (@lem5335839) (@lem5335843)). Qed.
Lemma lem5335845 : True = term431.
Proof. exact (SYM (@lem5335844)). Qed.
Lemma lem5335846 : term431.
Proof. exact (EQ_MP (@lem5335845) (@lem0)). Qed.
Lemma lem5335847 : term665 = term668.
Proof. exact (@lem5335836 (@lem5335846)). Qed.
Lemma lem5335849 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335850 : term364 = term365.
Proof. exact (@lem5335849 term157 term157). Qed.
Lemma lem5335851 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335852 : term367 = term157.
Proof. exact (EQ_MP (@lem5335851) (@lem940073)). Qed.
Lemma lem5335853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335854 : term365 = term305.
Proof. exact (MK_COMB (@lem5335853) (@lem5335852)). Qed.
Lemma lem5335855 : term364 = term305.
Proof. exact (TRANS (@lem5335850) (@lem5335854)). Qed.
Lemma lem5335857 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335858 : term443 = term293.
Proof. exact (@lem5335857 term157). Qed.
Lemma lem5335859 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5335860 : term669 = term663.
Proof. exact (MK_COMB (@lem5335859) (@lem5335858)). Qed.
Lemma lem5335861 : term668 = term431.
Proof. exact (MK_COMB (@lem5335860) (@lem5335855)). Qed.
Lemma lem5335863 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335864 : term431 = term432.
Proof. exact (@lem5335863 (NUMERAL 0) term157). Qed.
Lemma lem5335865 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335866 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335867 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335866 h1) (fun h1 : term432 = True => @lem5335865)). Qed.
Lemma lem5335868 : term432 = True.
Proof. exact (EQ_MP (@lem5335867) (@lem5335865)). Qed.
Lemma lem5335869 : term431 = True.
Proof. exact (TRANS (@lem5335864) (@lem5335868)). Qed.
Lemma lem5335870 : term668 = True.
Proof. exact (TRANS (@lem5335861) (@lem5335869)). Qed.
Lemma lem5335871 : term665 = True.
Proof. exact (TRANS (@lem5335847) (@lem5335870)). Qed.
Lemma lem5335872 : term431 = True.
Proof. exact (TRANS (@lem5335824) (@lem5335871)). Qed.
Lemma lem5335873 : term662 = True.
Proof. exact (TRANS (@lem5335815) (@lem5335872)). Qed.
Lemma lem5335874 : True = term662.
Proof. exact (SYM (@lem5335873)). Qed.
Lemma lem5335875 : term662.
Proof. exact (EQ_MP (@lem5335874) (@lem0)). Qed.
Lemma lem5335876 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term731 _69706 _69707.
Proof. exact (conj (@lem5335875) (@lem5335812 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335878 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5335879 (_69706 : int) (_69707 : int) : term732 _69706 _69707.
Proof. exact (@lem5335878 term305 (term412 _69706 _69707)). Qed.
Lemma lem5335880 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term733 _69706 _69707.
Proof. exact (@lem5335879 _69706 _69707 (@lem5335876 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335881 (_69706 : int) (_69707 : int) : (term734 _69706 _69707) = (term412 _69706 _69707).
Proof. exact (@lem1982733 (term412 _69706 _69707)). Qed.
Lemma lem5335882 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5335883 (_69706 : int) (_69707 : int) : (term735 _69706 _69707) = (term413 _69706 _69707).
Proof. exact (MK_COMB (@lem5335882) (@lem5335881 _69706 _69707)). Qed.
Lemma lem5335884 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5335885 (_69706 : int) (_69707 : int) : (term733 _69706 _69707) = (term414 _69706 _69707).
Proof. exact (MK_COMB (@lem5335883 _69706 _69707) (@lem5335884)). Qed.
Lemma lem5335886 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term414 _69706 _69707.
Proof. exact (EQ_MP (@lem5335885 _69706 _69707) (@lem5335880 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335887 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term500 _69706 _69707.
Proof. exact (conj (@lem5335886 _69704 _69706 _69705 _69707 h1) (@lem5335540 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335889 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5335890 (_69706 : int) (_69707 : int) : term736 _69706 _69707.
Proof. exact (@lem5335889 (term412 _69706 _69707) (term386 _69706 _69707)). Qed.
Lemma lem5335891 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term737 _69706 _69707.
Proof. exact (@lem5335890 _69706 _69707 (@lem5335887 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5335892 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = (term739 _69706 _69707).
Proof. exact (@lem1982753 (term380 _69706) (real_of_int _69706) (term740 _69707) (term380 _69707)). Qed.
Lemma lem5335893 (_69706 : int) : (term687 _69706) = (term688 _69706).
Proof. exact (@lem1982713 term355 (real_of_int _69706)). Qed.
Lemma lem5335895 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5335896 : term305 = term397.
Proof. exact (@lem5335895 term157). Qed.
Lemma lem5335898 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5335899 : term355 = term356.
Proof. exact (@lem5335898 term157). Qed.
Lemma lem5335900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335901 : term689 = term690.
Proof. exact (MK_COMB (@lem5335900) (@lem5335899)). Qed.
Lemma lem5335902 : term691 = term692.
Proof. exact (MK_COMB (@lem5335901) (@lem5335896)). Qed.
Lemma lem5335903 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5335905 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335906 : term431 = term432.
Proof. exact (@lem5335905 (NUMERAL 0) term157). Qed.
Lemma lem5335907 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335908 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335909 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335908 h1) (fun h1 : term432 = True => @lem5335907)). Qed.
Lemma lem5335910 : term432 = True.
Proof. exact (EQ_MP (@lem5335909) (@lem5335907)). Qed.
Lemma lem5335911 : term431 = True.
Proof. exact (TRANS (@lem5335906) (@lem5335910)). Qed.
Lemma lem5335912 : True = term431.
Proof. exact (SYM (@lem5335911)). Qed.
Lemma lem5335913 : term431.
Proof. exact (EQ_MP (@lem5335912) (@lem0)). Qed.
Lemma lem5335914 : term694.
Proof. exact (@lem5335903 (@lem5335913)). Qed.
Lemma lem5335916 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335917 : term431 = term432.
Proof. exact (@lem5335916 (NUMERAL 0) term157). Qed.
Lemma lem5335918 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335919 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335920 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335919 h1) (fun h1 : term432 = True => @lem5335918)). Qed.
Lemma lem5335921 : term432 = True.
Proof. exact (EQ_MP (@lem5335920) (@lem5335918)). Qed.
Lemma lem5335922 : term431 = True.
Proof. exact (TRANS (@lem5335917) (@lem5335921)). Qed.
Lemma lem5335923 : True = term431.
Proof. exact (SYM (@lem5335922)). Qed.
Lemma lem5335924 : term431.
Proof. exact (EQ_MP (@lem5335923) (@lem0)). Qed.
Lemma lem5335925 : term695.
Proof. exact (@lem5335914 (@lem5335924)). Qed.
Lemma lem5335927 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5335928 : term431 = term432.
Proof. exact (@lem5335927 (NUMERAL 0) term157). Qed.
Lemma lem5335929 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5335930 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5335931 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5335930 h1) (fun h1 : term432 = True => @lem5335929)). Qed.
Lemma lem5335932 : term432 = True.
Proof. exact (EQ_MP (@lem5335931) (@lem5335929)). Qed.
Lemma lem5335933 : term431 = True.
Proof. exact (TRANS (@lem5335928) (@lem5335932)). Qed.
Lemma lem5335934 : True = term431.
Proof. exact (SYM (@lem5335933)). Qed.
Lemma lem5335935 : term431.
Proof. exact (EQ_MP (@lem5335934) (@lem0)). Qed.
Lemma lem5335936 : term696.
Proof. exact (@lem5335925 (@lem5335935)). Qed.
Lemma lem5335938 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335939 : term364 = term365.
Proof. exact (@lem5335938 term157 term157). Qed.
Lemma lem5335940 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335941 : term367 = term157.
Proof. exact (EQ_MP (@lem5335940) (@lem940073)). Qed.
Lemma lem5335942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335943 : term365 = term305.
Proof. exact (MK_COMB (@lem5335942) (@lem5335941)). Qed.
Lemma lem5335944 : term364 = term305.
Proof. exact (TRANS (@lem5335939) (@lem5335943)). Qed.
Lemma lem5335946 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5335947 : term398 = term403.
Proof. exact (@lem5335946 term157 term157). Qed.
Lemma lem5335948 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335949 : term367 = term157.
Proof. exact (EQ_MP (@lem5335948) (@lem940073)). Qed.
Lemma lem5335950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335951 : term365 = term305.
Proof. exact (MK_COMB (@lem5335950) (@lem5335949)). Qed.
Lemma lem5335952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5335953 : term403 = term355.
Proof. exact (MK_COMB (@lem5335952) (@lem5335951)). Qed.
Lemma lem5335954 : term398 = term355.
Proof. exact (TRANS (@lem5335947) (@lem5335953)). Qed.
Lemma lem5335955 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5335956 : term697 = term689.
Proof. exact (MK_COMB (@lem5335955) (@lem5335954)). Qed.
Lemma lem5335957 : term698 = term691.
Proof. exact (MK_COMB (@lem5335956) (@lem5335944)). Qed.
Lemma lem5335959 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5335960 : term691 = term293.
Proof. exact (@lem5335959 term157). Qed.
Lemma lem5335961 : term698 = term293.
Proof. exact (TRANS (@lem5335957) (@lem5335960)). Qed.
Lemma lem5335962 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335963 : term700 = term441.
Proof. exact (MK_COMB (@lem5335962) (@lem5335961)). Qed.
Lemma lem5335964 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5335965 : term701 = term443.
Proof. exact (MK_COMB (@lem5335963) (@lem5335964)). Qed.
Lemma lem5335967 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335968 : term443 = term293.
Proof. exact (@lem5335967 term157). Qed.
Lemma lem5335969 : term701 = term293.
Proof. exact (TRANS (@lem5335965) (@lem5335968)). Qed.
Lemma lem5335971 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5335972 : term364 = term365.
Proof. exact (@lem5335971 term157 term157). Qed.
Lemma lem5335973 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5335974 : term367 = term157.
Proof. exact (EQ_MP (@lem5335973) (@lem940073)). Qed.
Lemma lem5335975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5335976 : term365 = term305.
Proof. exact (MK_COMB (@lem5335975) (@lem5335974)). Qed.
Lemma lem5335977 : term364 = term305.
Proof. exact (TRANS (@lem5335972) (@lem5335976)). Qed.
Lemma lem5335978 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5335979 : term445 = term443.
Proof. exact (MK_COMB (@lem5335978) (@lem5335977)). Qed.
Lemma lem5335981 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5335982 : term443 = term293.
Proof. exact (@lem5335981 term157). Qed.
Lemma lem5335983 : term445 = term293.
Proof. exact (TRANS (@lem5335979) (@lem5335982)). Qed.
Lemma lem5335984 : term293 = term445.
Proof. exact (SYM (@lem5335983)). Qed.
Lemma lem5335985 : term701 = term445.
Proof. exact (TRANS (@lem5335969) (@lem5335984)). Qed.
Lemma lem5335986 : term692 = term352.
Proof. exact (@lem5335936 (@lem5335985)). Qed.
Lemma lem5335987 : term691 = term352.
Proof. exact (TRANS (@lem5335902) (@lem5335986)). Qed.
Lemma lem5335989 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5335990 : term352 = term293.
Proof. exact (@lem5335989 term293). Qed.
Lemma lem5335991 : term691 = term293.
Proof. exact (TRANS (@lem5335987) (@lem5335990)). Qed.
Lemma lem5335992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5335993 : term702 = term441.
Proof. exact (MK_COMB (@lem5335992) (@lem5335991)). Qed.
Lemma lem5335994 (_69706 : int) : (real_of_int _69706) = (real_of_int _69706).
Proof. exact (eq_refl (real_of_int _69706)). Qed.
Lemma lem5335995 (_69706 : int) : (term688 _69706) = (term703 _69706).
Proof. exact (MK_COMB (@lem5335993) (@lem5335994 _69706)). Qed.
Lemma lem5335996 (_69706 : int) : (term687 _69706) = (term703 _69706).
Proof. exact (TRANS (@lem5335893 _69706) (@lem5335995 _69706)). Qed.
Lemma lem5335997 (_69706 : int) : (term703 _69706) = term293.
Proof. exact (@lem1982719 (real_of_int _69706)). Qed.
Lemma lem5335998 (_69706 : int) : (term687 _69706) = term293.
Proof. exact (TRANS (@lem5335996 _69706) (@lem5335997 _69706)). Qed.
Lemma lem5335999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336000 (_69706 : int) : (term704 _69706) = term705.
Proof. exact (MK_COMB (@lem5335999) (@lem5335998 _69706)). Qed.
Lemma lem5336001 (_69707 : int) : (term741 _69707) = (term707 _69707).
Proof. exact (@lem1982759 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5336002 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5336004 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336005 : term305 = term397.
Proof. exact (@lem5336004 term157). Qed.
Lemma lem5336007 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5336008 : term355 = term356.
Proof. exact (@lem5336007 term157). Qed.
Lemma lem5336009 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336010 : term689 = term690.
Proof. exact (MK_COMB (@lem5336009) (@lem5336008)). Qed.
Lemma lem5336011 : term691 = term692.
Proof. exact (MK_COMB (@lem5336010) (@lem5336005)). Qed.
Lemma lem5336012 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5336014 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336015 : term431 = term432.
Proof. exact (@lem5336014 (NUMERAL 0) term157). Qed.
Lemma lem5336016 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336017 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336018 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336017 h1) (fun h1 : term432 = True => @lem5336016)). Qed.
Lemma lem5336019 : term432 = True.
Proof. exact (EQ_MP (@lem5336018) (@lem5336016)). Qed.
Lemma lem5336020 : term431 = True.
Proof. exact (TRANS (@lem5336015) (@lem5336019)). Qed.
Lemma lem5336021 : True = term431.
Proof. exact (SYM (@lem5336020)). Qed.
Lemma lem5336022 : term431.
Proof. exact (EQ_MP (@lem5336021) (@lem0)). Qed.
Lemma lem5336023 : term694.
Proof. exact (@lem5336012 (@lem5336022)). Qed.
Lemma lem5336025 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336026 : term431 = term432.
Proof. exact (@lem5336025 (NUMERAL 0) term157). Qed.
Lemma lem5336027 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336028 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336029 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336028 h1) (fun h1 : term432 = True => @lem5336027)). Qed.
Lemma lem5336030 : term432 = True.
Proof. exact (EQ_MP (@lem5336029) (@lem5336027)). Qed.
Lemma lem5336031 : term431 = True.
Proof. exact (TRANS (@lem5336026) (@lem5336030)). Qed.
Lemma lem5336032 : True = term431.
Proof. exact (SYM (@lem5336031)). Qed.
Lemma lem5336033 : term431.
Proof. exact (EQ_MP (@lem5336032) (@lem0)). Qed.
Lemma lem5336034 : term695.
Proof. exact (@lem5336023 (@lem5336033)). Qed.
Lemma lem5336036 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336037 : term431 = term432.
Proof. exact (@lem5336036 (NUMERAL 0) term157). Qed.
Lemma lem5336038 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336039 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336040 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336039 h1) (fun h1 : term432 = True => @lem5336038)). Qed.
Lemma lem5336041 : term432 = True.
Proof. exact (EQ_MP (@lem5336040) (@lem5336038)). Qed.
Lemma lem5336042 : term431 = True.
Proof. exact (TRANS (@lem5336037) (@lem5336041)). Qed.
Lemma lem5336043 : True = term431.
Proof. exact (SYM (@lem5336042)). Qed.
Lemma lem5336044 : term431.
Proof. exact (EQ_MP (@lem5336043) (@lem0)). Qed.
Lemma lem5336045 : term696.
Proof. exact (@lem5336034 (@lem5336044)). Qed.
Lemma lem5336047 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336048 : term364 = term365.
Proof. exact (@lem5336047 term157 term157). Qed.
Lemma lem5336049 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336050 : term367 = term157.
Proof. exact (EQ_MP (@lem5336049) (@lem940073)). Qed.
Lemma lem5336051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336052 : term365 = term305.
Proof. exact (MK_COMB (@lem5336051) (@lem5336050)). Qed.
Lemma lem5336053 : term364 = term305.
Proof. exact (TRANS (@lem5336048) (@lem5336052)). Qed.
Lemma lem5336055 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5336056 : term398 = term403.
Proof. exact (@lem5336055 term157 term157). Qed.
Lemma lem5336057 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336058 : term367 = term157.
Proof. exact (EQ_MP (@lem5336057) (@lem940073)). Qed.
Lemma lem5336059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336060 : term365 = term305.
Proof. exact (MK_COMB (@lem5336059) (@lem5336058)). Qed.
Lemma lem5336061 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5336062 : term403 = term355.
Proof. exact (MK_COMB (@lem5336061) (@lem5336060)). Qed.
Lemma lem5336063 : term398 = term355.
Proof. exact (TRANS (@lem5336056) (@lem5336062)). Qed.
Lemma lem5336064 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336065 : term697 = term689.
Proof. exact (MK_COMB (@lem5336064) (@lem5336063)). Qed.
Lemma lem5336066 : term698 = term691.
Proof. exact (MK_COMB (@lem5336065) (@lem5336053)). Qed.
Lemma lem5336068 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5336069 : term691 = term293.
Proof. exact (@lem5336068 term157). Qed.
Lemma lem5336070 : term698 = term293.
Proof. exact (TRANS (@lem5336066) (@lem5336069)). Qed.
Lemma lem5336071 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336072 : term700 = term441.
Proof. exact (MK_COMB (@lem5336071) (@lem5336070)). Qed.
Lemma lem5336073 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5336074 : term701 = term443.
Proof. exact (MK_COMB (@lem5336072) (@lem5336073)). Qed.
Lemma lem5336076 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336077 : term443 = term293.
Proof. exact (@lem5336076 term157). Qed.
Lemma lem5336078 : term701 = term293.
Proof. exact (TRANS (@lem5336074) (@lem5336077)). Qed.
Lemma lem5336080 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336081 : term364 = term365.
Proof. exact (@lem5336080 term157 term157). Qed.
Lemma lem5336082 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336083 : term367 = term157.
Proof. exact (EQ_MP (@lem5336082) (@lem940073)). Qed.
Lemma lem5336084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336085 : term365 = term305.
Proof. exact (MK_COMB (@lem5336084) (@lem5336083)). Qed.
Lemma lem5336086 : term364 = term305.
Proof. exact (TRANS (@lem5336081) (@lem5336085)). Qed.
Lemma lem5336087 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5336088 : term445 = term443.
Proof. exact (MK_COMB (@lem5336087) (@lem5336086)). Qed.
Lemma lem5336090 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336091 : term443 = term293.
Proof. exact (@lem5336090 term157). Qed.
Lemma lem5336092 : term445 = term293.
Proof. exact (TRANS (@lem5336088) (@lem5336091)). Qed.
Lemma lem5336093 : term293 = term445.
Proof. exact (SYM (@lem5336092)). Qed.
Lemma lem5336094 : term701 = term445.
Proof. exact (TRANS (@lem5336078) (@lem5336093)). Qed.
Lemma lem5336095 : term692 = term352.
Proof. exact (@lem5336045 (@lem5336094)). Qed.
Lemma lem5336096 : term691 = term352.
Proof. exact (TRANS (@lem5336011) (@lem5336095)). Qed.
Lemma lem5336098 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5336099 : term352 = term293.
Proof. exact (@lem5336098 term293). Qed.
Lemma lem5336100 : term691 = term293.
Proof. exact (TRANS (@lem5336096) (@lem5336099)). Qed.
Lemma lem5336101 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336102 : term702 = term441.
Proof. exact (MK_COMB (@lem5336101) (@lem5336100)). Qed.
Lemma lem5336103 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5336104 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5336102) (@lem5336103 _69707)). Qed.
Lemma lem5336105 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5336002 _69707) (@lem5336104 _69707)). Qed.
Lemma lem5336106 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5336107 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5336105 _69707) (@lem5336106 _69707)). Qed.
Lemma lem5336108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336109 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5336108) (@lem5336107 _69707)). Qed.
Lemma lem5336110 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5336111 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5336109 _69707) (@lem5336110)). Qed.
Lemma lem5336112 (_69707 : int) : (term741 _69707) = term710.
Proof. exact (TRANS (@lem5336001 _69707) (@lem5336111 _69707)). Qed.
Lemma lem5336113 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5336114 (_69707 : int) : (term741 _69707) = term355.
Proof. exact (TRANS (@lem5336112 _69707) (@lem5336113)). Qed.
Lemma lem5336115 (_69706 : int) (_69707 : int) : (term739 _69706 _69707) = term710.
Proof. exact (MK_COMB (@lem5336000 _69706) (@lem5336114 _69707)). Qed.
Lemma lem5336116 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = term710.
Proof. exact (TRANS (@lem5335892 _69706 _69707) (@lem5336115 _69706 _69707)). Qed.
Lemma lem5336117 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5336118 (_69706 : int) (_69707 : int) : (term738 _69706 _69707) = term355.
Proof. exact (TRANS (@lem5336116 _69706 _69707) (@lem5336117)). Qed.
Lemma lem5336119 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5336120 (_69706 : int) (_69707 : int) : (term742 _69706 _69707) = term712.
Proof. exact (MK_COMB (@lem5336119) (@lem5336118 _69706 _69707)). Qed.
Lemma lem5336121 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5336122 (_69706 : int) (_69707 : int) : (term737 _69706 _69707) = term713.
Proof. exact (MK_COMB (@lem5336120 _69706 _69707) (@lem5336121)). Qed.
Lemma lem5336123 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5336122 _69706 _69707) (@lem5335891 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336125 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5336126 : term713 = term714.
Proof. exact (@lem5336125 term293 term355). Qed.
Lemma lem5336128 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5336129 : term355 = term356.
Proof. exact (@lem5336128 term157). Qed.
Lemma lem5336131 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336132 : term293 = term352.
Proof. exact (@lem5336131 (NUMERAL 0)). Qed.
Lemma lem5336133 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5336134 : term295 = term715.
Proof. exact (MK_COMB (@lem5336133) (@lem5336132)). Qed.
Lemma lem5336135 : term714 = term716.
Proof. exact (MK_COMB (@lem5336134) (@lem5336129)). Qed.
Lemma lem5336136 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5336138 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336139 : term431 = term432.
Proof. exact (@lem5336138 (NUMERAL 0) term157). Qed.
Lemma lem5336140 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336141 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336142 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336141 h1) (fun h1 : term432 = True => @lem5336140)). Qed.
Lemma lem5336143 : term432 = True.
Proof. exact (EQ_MP (@lem5336142) (@lem5336140)). Qed.
Lemma lem5336144 : term431 = True.
Proof. exact (TRANS (@lem5336139) (@lem5336143)). Qed.
Lemma lem5336145 : True = term431.
Proof. exact (SYM (@lem5336144)). Qed.
Lemma lem5336146 : term431.
Proof. exact (EQ_MP (@lem5336145) (@lem0)). Qed.
Lemma lem5336147 : term718.
Proof. exact (@lem5336136 (@lem5336146)). Qed.
Lemma lem5336149 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336150 : term431 = term432.
Proof. exact (@lem5336149 (NUMERAL 0) term157). Qed.
Lemma lem5336151 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336152 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336153 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336152 h1) (fun h1 : term432 = True => @lem5336151)). Qed.
Lemma lem5336154 : term432 = True.
Proof. exact (EQ_MP (@lem5336153) (@lem5336151)). Qed.
Lemma lem5336155 : term431 = True.
Proof. exact (TRANS (@lem5336150) (@lem5336154)). Qed.
Lemma lem5336156 : True = term431.
Proof. exact (SYM (@lem5336155)). Qed.
Lemma lem5336157 : term431.
Proof. exact (EQ_MP (@lem5336156) (@lem0)). Qed.
Lemma lem5336158 : term716 = term719.
Proof. exact (@lem5336147 (@lem5336157)). Qed.
Lemma lem5336160 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5336161 : term398 = term403.
Proof. exact (@lem5336160 term157 term157). Qed.
Lemma lem5336162 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336163 : term367 = term157.
Proof. exact (EQ_MP (@lem5336162) (@lem940073)). Qed.
Lemma lem5336164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336165 : term365 = term305.
Proof. exact (MK_COMB (@lem5336164) (@lem5336163)). Qed.
Lemma lem5336166 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5336167 : term403 = term355.
Proof. exact (MK_COMB (@lem5336166) (@lem5336165)). Qed.
Lemma lem5336168 : term398 = term355.
Proof. exact (TRANS (@lem5336161) (@lem5336167)). Qed.
Lemma lem5336170 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336171 : term443 = term293.
Proof. exact (@lem5336170 term157). Qed.
Lemma lem5336172 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5336173 : term720 = term295.
Proof. exact (MK_COMB (@lem5336172) (@lem5336171)). Qed.
Lemma lem5336174 : term719 = term714.
Proof. exact (MK_COMB (@lem5336173) (@lem5336168)). Qed.
Lemma lem5336176 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5336177 : term714 = term723.
Proof. exact (@lem5336176 (NUMERAL 0) term157). Qed.
Lemma lem5336178 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336179 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5336180 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336179 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5336178)). Qed.
Lemma lem5336181 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5336180) (@lem5336178)). Qed.
Lemma lem5336182 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5336183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5336184 : term724 = (and True).
Proof. exact (MK_COMB (@lem5336183) (@lem5336182)). Qed.
Lemma lem5336185 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5336184) (@lem5336181)). Qed.
Lemma lem5336187 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5336188 : term723 = False.
Proof. exact (TRANS (@lem5336185) (@lem5336187)). Qed.
Lemma lem5336189 : term714 = False.
Proof. exact (TRANS (@lem5336177) (@lem5336188)). Qed.
Lemma lem5336190 : term719 = False.
Proof. exact (TRANS (@lem5336174) (@lem5336189)). Qed.
Lemma lem5336191 : term716 = False.
Proof. exact (TRANS (@lem5336158) (@lem5336190)). Qed.
Lemma lem5336192 : term714 = False.
Proof. exact (TRANS (@lem5336135) (@lem5336191)). Qed.
Lemma lem5336193 : term713 = False.
Proof. exact (TRANS (@lem5336126) (@lem5336192)). Qed.
Lemma lem5336194 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term767 _69704 _69706 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5336193) (@lem5336123 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336195 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term776 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5336196 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term637 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5336195 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336198 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term606 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5336196 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336200 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term575 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5336198 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336202 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term544 _69704 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5336200 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336204 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term513 _69706 _69705 _69707.
Proof. exact (proj2 (@lem5336202 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336208 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term414 _69705 _69707.
Proof. exact (proj2 (@lem5336204 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336209 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term460 _69706 _69705 _69707.
Proof. exact (proj1 (@lem5336204 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336210 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term389 _69705 _69707.
Proof. exact (proj2 (@lem5336209 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336213 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5336214 : term662 = term431.
Proof. exact (@lem5336213 term293 term305). Qed.
Lemma lem5336216 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336217 : term305 = term397.
Proof. exact (@lem5336216 term157). Qed.
Lemma lem5336219 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336220 : term293 = term352.
Proof. exact (@lem5336219 (NUMERAL 0)). Qed.
Lemma lem5336221 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5336222 : term663 = term664.
Proof. exact (MK_COMB (@lem5336221) (@lem5336220)). Qed.
Lemma lem5336223 : term431 = term665.
Proof. exact (MK_COMB (@lem5336222) (@lem5336217)). Qed.
Lemma lem5336224 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5336226 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336227 : term431 = term432.
Proof. exact (@lem5336226 (NUMERAL 0) term157). Qed.
Lemma lem5336228 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336229 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336230 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336229 h1) (fun h1 : term432 = True => @lem5336228)). Qed.
Lemma lem5336231 : term432 = True.
Proof. exact (EQ_MP (@lem5336230) (@lem5336228)). Qed.
Lemma lem5336232 : term431 = True.
Proof. exact (TRANS (@lem5336227) (@lem5336231)). Qed.
Lemma lem5336233 : True = term431.
Proof. exact (SYM (@lem5336232)). Qed.
Lemma lem5336234 : term431.
Proof. exact (EQ_MP (@lem5336233) (@lem0)). Qed.
Lemma lem5336235 : term667.
Proof. exact (@lem5336224 (@lem5336234)). Qed.
Lemma lem5336237 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336238 : term431 = term432.
Proof. exact (@lem5336237 (NUMERAL 0) term157). Qed.
Lemma lem5336239 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336240 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336241 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336240 h1) (fun h1 : term432 = True => @lem5336239)). Qed.
Lemma lem5336242 : term432 = True.
Proof. exact (EQ_MP (@lem5336241) (@lem5336239)). Qed.
Lemma lem5336243 : term431 = True.
Proof. exact (TRANS (@lem5336238) (@lem5336242)). Qed.
Lemma lem5336244 : True = term431.
Proof. exact (SYM (@lem5336243)). Qed.
Lemma lem5336245 : term431.
Proof. exact (EQ_MP (@lem5336244) (@lem0)). Qed.
Lemma lem5336246 : term665 = term668.
Proof. exact (@lem5336235 (@lem5336245)). Qed.
Lemma lem5336248 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336249 : term364 = term365.
Proof. exact (@lem5336248 term157 term157). Qed.
Lemma lem5336250 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336251 : term367 = term157.
Proof. exact (EQ_MP (@lem5336250) (@lem940073)). Qed.
Lemma lem5336252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336253 : term365 = term305.
Proof. exact (MK_COMB (@lem5336252) (@lem5336251)). Qed.
Lemma lem5336254 : term364 = term305.
Proof. exact (TRANS (@lem5336249) (@lem5336253)). Qed.
Lemma lem5336256 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336257 : term443 = term293.
Proof. exact (@lem5336256 term157). Qed.
Lemma lem5336258 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5336259 : term669 = term663.
Proof. exact (MK_COMB (@lem5336258) (@lem5336257)). Qed.
Lemma lem5336260 : term668 = term431.
Proof. exact (MK_COMB (@lem5336259) (@lem5336254)). Qed.
Lemma lem5336262 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336263 : term431 = term432.
Proof. exact (@lem5336262 (NUMERAL 0) term157). Qed.
Lemma lem5336264 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336265 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336266 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336265 h1) (fun h1 : term432 = True => @lem5336264)). Qed.
Lemma lem5336267 : term432 = True.
Proof. exact (EQ_MP (@lem5336266) (@lem5336264)). Qed.
Lemma lem5336268 : term431 = True.
Proof. exact (TRANS (@lem5336263) (@lem5336267)). Qed.
Lemma lem5336269 : term668 = True.
Proof. exact (TRANS (@lem5336260) (@lem5336268)). Qed.
Lemma lem5336270 : term665 = True.
Proof. exact (TRANS (@lem5336246) (@lem5336269)). Qed.
Lemma lem5336271 : term431 = True.
Proof. exact (TRANS (@lem5336223) (@lem5336270)). Qed.
Lemma lem5336272 : term662 = True.
Proof. exact (TRANS (@lem5336214) (@lem5336271)). Qed.
Lemma lem5336273 : True = term662.
Proof. exact (SYM (@lem5336272)). Qed.
Lemma lem5336274 : term662.
Proof. exact (EQ_MP (@lem5336273) (@lem0)). Qed.
Lemma lem5336275 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term726 _69705 _69707.
Proof. exact (conj (@lem5336274) (@lem5336210 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336277 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5336278 (_69705 : int) (_69707 : int) : term727 _69705 _69707.
Proof. exact (@lem5336277 term305 (term386 _69705 _69707)). Qed.
Lemma lem5336279 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term728 _69705 _69707.
Proof. exact (@lem5336278 _69705 _69707 (@lem5336275 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336280 (_69705 : int) (_69707 : int) : (term729 _69705 _69707) = (term386 _69705 _69707).
Proof. exact (@lem1982733 (term386 _69705 _69707)). Qed.
Lemma lem5336281 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5336282 (_69705 : int) (_69707 : int) : (term730 _69705 _69707) = (term388 _69705 _69707).
Proof. exact (MK_COMB (@lem5336281) (@lem5336280 _69705 _69707)). Qed.
Lemma lem5336283 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5336284 (_69705 : int) (_69707 : int) : (term728 _69705 _69707) = (term389 _69705 _69707).
Proof. exact (MK_COMB (@lem5336282 _69705 _69707) (@lem5336283)). Qed.
Lemma lem5336285 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term389 _69705 _69707.
Proof. exact (EQ_MP (@lem5336284 _69705 _69707) (@lem5336279 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336287 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5336288 : term662 = term431.
Proof. exact (@lem5336287 term293 term305). Qed.
Lemma lem5336290 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336291 : term305 = term397.
Proof. exact (@lem5336290 term157). Qed.
Lemma lem5336293 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336294 : term293 = term352.
Proof. exact (@lem5336293 (NUMERAL 0)). Qed.
Lemma lem5336295 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5336296 : term663 = term664.
Proof. exact (MK_COMB (@lem5336295) (@lem5336294)). Qed.
Lemma lem5336297 : term431 = term665.
Proof. exact (MK_COMB (@lem5336296) (@lem5336291)). Qed.
Lemma lem5336298 : term666.
Proof. exact (@lem1980255 term293 term305 term305 term305). Qed.
Lemma lem5336300 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336301 : term431 = term432.
Proof. exact (@lem5336300 (NUMERAL 0) term157). Qed.
Lemma lem5336302 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336303 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336304 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336303 h1) (fun h1 : term432 = True => @lem5336302)). Qed.
Lemma lem5336305 : term432 = True.
Proof. exact (EQ_MP (@lem5336304) (@lem5336302)). Qed.
Lemma lem5336306 : term431 = True.
Proof. exact (TRANS (@lem5336301) (@lem5336305)). Qed.
Lemma lem5336307 : True = term431.
Proof. exact (SYM (@lem5336306)). Qed.
Lemma lem5336308 : term431.
Proof. exact (EQ_MP (@lem5336307) (@lem0)). Qed.
Lemma lem5336309 : term667.
Proof. exact (@lem5336298 (@lem5336308)). Qed.
Lemma lem5336311 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336312 : term431 = term432.
Proof. exact (@lem5336311 (NUMERAL 0) term157). Qed.
Lemma lem5336313 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336314 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336315 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336314 h1) (fun h1 : term432 = True => @lem5336313)). Qed.
Lemma lem5336316 : term432 = True.
Proof. exact (EQ_MP (@lem5336315) (@lem5336313)). Qed.
Lemma lem5336317 : term431 = True.
Proof. exact (TRANS (@lem5336312) (@lem5336316)). Qed.
Lemma lem5336318 : True = term431.
Proof. exact (SYM (@lem5336317)). Qed.
Lemma lem5336319 : term431.
Proof. exact (EQ_MP (@lem5336318) (@lem0)). Qed.
Lemma lem5336320 : term665 = term668.
Proof. exact (@lem5336309 (@lem5336319)). Qed.
Lemma lem5336322 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336323 : term364 = term365.
Proof. exact (@lem5336322 term157 term157). Qed.
Lemma lem5336324 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336325 : term367 = term157.
Proof. exact (EQ_MP (@lem5336324) (@lem940073)). Qed.
Lemma lem5336326 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336327 : term365 = term305.
Proof. exact (MK_COMB (@lem5336326) (@lem5336325)). Qed.
Lemma lem5336328 : term364 = term305.
Proof. exact (TRANS (@lem5336323) (@lem5336327)). Qed.
Lemma lem5336330 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336331 : term443 = term293.
Proof. exact (@lem5336330 term157). Qed.
Lemma lem5336332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5336333 : term669 = term663.
Proof. exact (MK_COMB (@lem5336332) (@lem5336331)). Qed.
Lemma lem5336334 : term668 = term431.
Proof. exact (MK_COMB (@lem5336333) (@lem5336328)). Qed.
Lemma lem5336336 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336337 : term431 = term432.
Proof. exact (@lem5336336 (NUMERAL 0) term157). Qed.
Lemma lem5336338 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336339 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336340 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336339 h1) (fun h1 : term432 = True => @lem5336338)). Qed.
Lemma lem5336341 : term432 = True.
Proof. exact (EQ_MP (@lem5336340) (@lem5336338)). Qed.
Lemma lem5336342 : term431 = True.
Proof. exact (TRANS (@lem5336337) (@lem5336341)). Qed.
Lemma lem5336343 : term668 = True.
Proof. exact (TRANS (@lem5336334) (@lem5336342)). Qed.
Lemma lem5336344 : term665 = True.
Proof. exact (TRANS (@lem5336320) (@lem5336343)). Qed.
Lemma lem5336345 : term431 = True.
Proof. exact (TRANS (@lem5336297) (@lem5336344)). Qed.
Lemma lem5336346 : term662 = True.
Proof. exact (TRANS (@lem5336288) (@lem5336345)). Qed.
Lemma lem5336347 : True = term662.
Proof. exact (SYM (@lem5336346)). Qed.
Lemma lem5336348 : term662.
Proof. exact (EQ_MP (@lem5336347) (@lem0)). Qed.
Lemma lem5336349 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term731 _69705 _69707.
Proof. exact (conj (@lem5336348) (@lem5336208 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336351 (x : real) (y : real) : term671 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5336352 (_69705 : int) (_69707 : int) : term732 _69705 _69707.
Proof. exact (@lem5336351 term305 (term412 _69705 _69707)). Qed.
Lemma lem5336353 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term733 _69705 _69707.
Proof. exact (@lem5336352 _69705 _69707 (@lem5336349 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336354 (_69705 : int) (_69707 : int) : (term734 _69705 _69707) = (term412 _69705 _69707).
Proof. exact (@lem1982733 (term412 _69705 _69707)). Qed.
Lemma lem5336355 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5336356 (_69705 : int) (_69707 : int) : (term735 _69705 _69707) = (term413 _69705 _69707).
Proof. exact (MK_COMB (@lem5336355) (@lem5336354 _69705 _69707)). Qed.
Lemma lem5336357 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5336358 (_69705 : int) (_69707 : int) : (term733 _69705 _69707) = (term414 _69705 _69707).
Proof. exact (MK_COMB (@lem5336356 _69705 _69707) (@lem5336357)). Qed.
Lemma lem5336359 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term414 _69705 _69707.
Proof. exact (EQ_MP (@lem5336358 _69705 _69707) (@lem5336353 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336360 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term500 _69705 _69707.
Proof. exact (conj (@lem5336359 _69704 _69706 _69705 _69707 h1) (@lem5336285 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336362 (x : real) (y : real) : term682 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5336363 (_69705 : int) (_69707 : int) : term736 _69705 _69707.
Proof. exact (@lem5336362 (term412 _69705 _69707) (term386 _69705 _69707)). Qed.
Lemma lem5336364 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term737 _69705 _69707.
Proof. exact (@lem5336363 _69705 _69707 (@lem5336360 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336365 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = (term739 _69705 _69707).
Proof. exact (@lem1982753 (term380 _69705) (real_of_int _69705) (term740 _69707) (term380 _69707)). Qed.
Lemma lem5336366 (_69705 : int) : (term687 _69705) = (term688 _69705).
Proof. exact (@lem1982713 term355 (real_of_int _69705)). Qed.
Lemma lem5336368 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336369 : term305 = term397.
Proof. exact (@lem5336368 term157). Qed.
Lemma lem5336371 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5336372 : term355 = term356.
Proof. exact (@lem5336371 term157). Qed.
Lemma lem5336373 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336374 : term689 = term690.
Proof. exact (MK_COMB (@lem5336373) (@lem5336372)). Qed.
Lemma lem5336375 : term691 = term692.
Proof. exact (MK_COMB (@lem5336374) (@lem5336369)). Qed.
Lemma lem5336376 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5336378 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336379 : term431 = term432.
Proof. exact (@lem5336378 (NUMERAL 0) term157). Qed.
Lemma lem5336380 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336381 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336382 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336381 h1) (fun h1 : term432 = True => @lem5336380)). Qed.
Lemma lem5336383 : term432 = True.
Proof. exact (EQ_MP (@lem5336382) (@lem5336380)). Qed.
Lemma lem5336384 : term431 = True.
Proof. exact (TRANS (@lem5336379) (@lem5336383)). Qed.
Lemma lem5336385 : True = term431.
Proof. exact (SYM (@lem5336384)). Qed.
Lemma lem5336386 : term431.
Proof. exact (EQ_MP (@lem5336385) (@lem0)). Qed.
Lemma lem5336387 : term694.
Proof. exact (@lem5336376 (@lem5336386)). Qed.
Lemma lem5336389 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336390 : term431 = term432.
Proof. exact (@lem5336389 (NUMERAL 0) term157). Qed.
Lemma lem5336391 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336392 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336393 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336392 h1) (fun h1 : term432 = True => @lem5336391)). Qed.
Lemma lem5336394 : term432 = True.
Proof. exact (EQ_MP (@lem5336393) (@lem5336391)). Qed.
Lemma lem5336395 : term431 = True.
Proof. exact (TRANS (@lem5336390) (@lem5336394)). Qed.
Lemma lem5336396 : True = term431.
Proof. exact (SYM (@lem5336395)). Qed.
Lemma lem5336397 : term431.
Proof. exact (EQ_MP (@lem5336396) (@lem0)). Qed.
Lemma lem5336398 : term695.
Proof. exact (@lem5336387 (@lem5336397)). Qed.
Lemma lem5336400 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336401 : term431 = term432.
Proof. exact (@lem5336400 (NUMERAL 0) term157). Qed.
Lemma lem5336402 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336403 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336404 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336403 h1) (fun h1 : term432 = True => @lem5336402)). Qed.
Lemma lem5336405 : term432 = True.
Proof. exact (EQ_MP (@lem5336404) (@lem5336402)). Qed.
Lemma lem5336406 : term431 = True.
Proof. exact (TRANS (@lem5336401) (@lem5336405)). Qed.
Lemma lem5336407 : True = term431.
Proof. exact (SYM (@lem5336406)). Qed.
Lemma lem5336408 : term431.
Proof. exact (EQ_MP (@lem5336407) (@lem0)). Qed.
Lemma lem5336409 : term696.
Proof. exact (@lem5336398 (@lem5336408)). Qed.
Lemma lem5336411 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336412 : term364 = term365.
Proof. exact (@lem5336411 term157 term157). Qed.
Lemma lem5336413 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336414 : term367 = term157.
Proof. exact (EQ_MP (@lem5336413) (@lem940073)). Qed.
Lemma lem5336415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336416 : term365 = term305.
Proof. exact (MK_COMB (@lem5336415) (@lem5336414)). Qed.
Lemma lem5336417 : term364 = term305.
Proof. exact (TRANS (@lem5336412) (@lem5336416)). Qed.
Lemma lem5336419 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5336420 : term398 = term403.
Proof. exact (@lem5336419 term157 term157). Qed.
Lemma lem5336421 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336422 : term367 = term157.
Proof. exact (EQ_MP (@lem5336421) (@lem940073)). Qed.
Lemma lem5336423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336424 : term365 = term305.
Proof. exact (MK_COMB (@lem5336423) (@lem5336422)). Qed.
Lemma lem5336425 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5336426 : term403 = term355.
Proof. exact (MK_COMB (@lem5336425) (@lem5336424)). Qed.
Lemma lem5336427 : term398 = term355.
Proof. exact (TRANS (@lem5336420) (@lem5336426)). Qed.
Lemma lem5336428 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336429 : term697 = term689.
Proof. exact (MK_COMB (@lem5336428) (@lem5336427)). Qed.
Lemma lem5336430 : term698 = term691.
Proof. exact (MK_COMB (@lem5336429) (@lem5336417)). Qed.
Lemma lem5336432 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5336433 : term691 = term293.
Proof. exact (@lem5336432 term157). Qed.
Lemma lem5336434 : term698 = term293.
Proof. exact (TRANS (@lem5336430) (@lem5336433)). Qed.
Lemma lem5336435 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336436 : term700 = term441.
Proof. exact (MK_COMB (@lem5336435) (@lem5336434)). Qed.
Lemma lem5336437 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5336438 : term701 = term443.
Proof. exact (MK_COMB (@lem5336436) (@lem5336437)). Qed.
Lemma lem5336440 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336441 : term443 = term293.
Proof. exact (@lem5336440 term157). Qed.
Lemma lem5336442 : term701 = term293.
Proof. exact (TRANS (@lem5336438) (@lem5336441)). Qed.
Lemma lem5336444 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336445 : term364 = term365.
Proof. exact (@lem5336444 term157 term157). Qed.
Lemma lem5336446 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336447 : term367 = term157.
Proof. exact (EQ_MP (@lem5336446) (@lem940073)). Qed.
Lemma lem5336448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336449 : term365 = term305.
Proof. exact (MK_COMB (@lem5336448) (@lem5336447)). Qed.
Lemma lem5336450 : term364 = term305.
Proof. exact (TRANS (@lem5336445) (@lem5336449)). Qed.
Lemma lem5336451 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5336452 : term445 = term443.
Proof. exact (MK_COMB (@lem5336451) (@lem5336450)). Qed.
Lemma lem5336454 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336455 : term443 = term293.
Proof. exact (@lem5336454 term157). Qed.
Lemma lem5336456 : term445 = term293.
Proof. exact (TRANS (@lem5336452) (@lem5336455)). Qed.
Lemma lem5336457 : term293 = term445.
Proof. exact (SYM (@lem5336456)). Qed.
Lemma lem5336458 : term701 = term445.
Proof. exact (TRANS (@lem5336442) (@lem5336457)). Qed.
Lemma lem5336459 : term692 = term352.
Proof. exact (@lem5336409 (@lem5336458)). Qed.
Lemma lem5336460 : term691 = term352.
Proof. exact (TRANS (@lem5336375) (@lem5336459)). Qed.
Lemma lem5336462 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5336463 : term352 = term293.
Proof. exact (@lem5336462 term293). Qed.
Lemma lem5336464 : term691 = term293.
Proof. exact (TRANS (@lem5336460) (@lem5336463)). Qed.
Lemma lem5336465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336466 : term702 = term441.
Proof. exact (MK_COMB (@lem5336465) (@lem5336464)). Qed.
Lemma lem5336467 (_69705 : int) : (real_of_int _69705) = (real_of_int _69705).
Proof. exact (eq_refl (real_of_int _69705)). Qed.
Lemma lem5336468 (_69705 : int) : (term688 _69705) = (term703 _69705).
Proof. exact (MK_COMB (@lem5336466) (@lem5336467 _69705)). Qed.
Lemma lem5336469 (_69705 : int) : (term687 _69705) = (term703 _69705).
Proof. exact (TRANS (@lem5336366 _69705) (@lem5336468 _69705)). Qed.
Lemma lem5336470 (_69705 : int) : (term703 _69705) = term293.
Proof. exact (@lem1982719 (real_of_int _69705)). Qed.
Lemma lem5336471 (_69705 : int) : (term687 _69705) = term293.
Proof. exact (TRANS (@lem5336469 _69705) (@lem5336470 _69705)). Qed.
Lemma lem5336472 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336473 (_69705 : int) : (term704 _69705) = term705.
Proof. exact (MK_COMB (@lem5336472) (@lem5336471 _69705)). Qed.
Lemma lem5336474 (_69707 : int) : (term741 _69707) = (term707 _69707).
Proof. exact (@lem1982759 (real_of_int _69707) (term380 _69707) term355). Qed.
Lemma lem5336475 (_69707 : int) : (term708 _69707) = (term688 _69707).
Proof. exact (@lem1982715 term355 (real_of_int _69707)). Qed.
Lemma lem5336477 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336478 : term305 = term397.
Proof. exact (@lem5336477 term157). Qed.
Lemma lem5336480 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5336481 : term355 = term356.
Proof. exact (@lem5336480 term157). Qed.
Lemma lem5336482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336483 : term689 = term690.
Proof. exact (MK_COMB (@lem5336482) (@lem5336481)). Qed.
Lemma lem5336484 : term691 = term692.
Proof. exact (MK_COMB (@lem5336483) (@lem5336478)). Qed.
Lemma lem5336485 : term693.
Proof. exact (@lem1981473 term355 term305 term305 term305 term293 term305). Qed.
Lemma lem5336487 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336488 : term431 = term432.
Proof. exact (@lem5336487 (NUMERAL 0) term157). Qed.
Lemma lem5336489 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336490 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336491 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336490 h1) (fun h1 : term432 = True => @lem5336489)). Qed.
Lemma lem5336492 : term432 = True.
Proof. exact (EQ_MP (@lem5336491) (@lem5336489)). Qed.
Lemma lem5336493 : term431 = True.
Proof. exact (TRANS (@lem5336488) (@lem5336492)). Qed.
Lemma lem5336494 : True = term431.
Proof. exact (SYM (@lem5336493)). Qed.
Lemma lem5336495 : term431.
Proof. exact (EQ_MP (@lem5336494) (@lem0)). Qed.
Lemma lem5336496 : term694.
Proof. exact (@lem5336485 (@lem5336495)). Qed.
Lemma lem5336498 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336499 : term431 = term432.
Proof. exact (@lem5336498 (NUMERAL 0) term157). Qed.
Lemma lem5336500 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336501 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336502 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336501 h1) (fun h1 : term432 = True => @lem5336500)). Qed.
Lemma lem5336503 : term432 = True.
Proof. exact (EQ_MP (@lem5336502) (@lem5336500)). Qed.
Lemma lem5336504 : term431 = True.
Proof. exact (TRANS (@lem5336499) (@lem5336503)). Qed.
Lemma lem5336505 : True = term431.
Proof. exact (SYM (@lem5336504)). Qed.
Lemma lem5336506 : term431.
Proof. exact (EQ_MP (@lem5336505) (@lem0)). Qed.
Lemma lem5336507 : term695.
Proof. exact (@lem5336496 (@lem5336506)). Qed.
Lemma lem5336509 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336510 : term431 = term432.
Proof. exact (@lem5336509 (NUMERAL 0) term157). Qed.
Lemma lem5336511 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336512 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336513 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336512 h1) (fun h1 : term432 = True => @lem5336511)). Qed.
Lemma lem5336514 : term432 = True.
Proof. exact (EQ_MP (@lem5336513) (@lem5336511)). Qed.
Lemma lem5336515 : term431 = True.
Proof. exact (TRANS (@lem5336510) (@lem5336514)). Qed.
Lemma lem5336516 : True = term431.
Proof. exact (SYM (@lem5336515)). Qed.
Lemma lem5336517 : term431.
Proof. exact (EQ_MP (@lem5336516) (@lem0)). Qed.
Lemma lem5336518 : term696.
Proof. exact (@lem5336507 (@lem5336517)). Qed.
Lemma lem5336520 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336521 : term364 = term365.
Proof. exact (@lem5336520 term157 term157). Qed.
Lemma lem5336522 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336523 : term367 = term157.
Proof. exact (EQ_MP (@lem5336522) (@lem940073)). Qed.
Lemma lem5336524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336525 : term365 = term305.
Proof. exact (MK_COMB (@lem5336524) (@lem5336523)). Qed.
Lemma lem5336526 : term364 = term305.
Proof. exact (TRANS (@lem5336521) (@lem5336525)). Qed.
Lemma lem5336528 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5336529 : term398 = term403.
Proof. exact (@lem5336528 term157 term157). Qed.
Lemma lem5336530 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336531 : term367 = term157.
Proof. exact (EQ_MP (@lem5336530) (@lem940073)). Qed.
Lemma lem5336532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336533 : term365 = term305.
Proof. exact (MK_COMB (@lem5336532) (@lem5336531)). Qed.
Lemma lem5336534 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5336535 : term403 = term355.
Proof. exact (MK_COMB (@lem5336534) (@lem5336533)). Qed.
Lemma lem5336536 : term398 = term355.
Proof. exact (TRANS (@lem5336529) (@lem5336535)). Qed.
Lemma lem5336537 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336538 : term697 = term689.
Proof. exact (MK_COMB (@lem5336537) (@lem5336536)). Qed.
Lemma lem5336539 : term698 = term691.
Proof. exact (MK_COMB (@lem5336538) (@lem5336526)). Qed.
Lemma lem5336541 (m : nat) : (term699 m) = term293.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5336542 : term691 = term293.
Proof. exact (@lem5336541 term157). Qed.
Lemma lem5336543 : term698 = term293.
Proof. exact (TRANS (@lem5336539) (@lem5336542)). Qed.
Lemma lem5336544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336545 : term700 = term441.
Proof. exact (MK_COMB (@lem5336544) (@lem5336543)). Qed.
Lemma lem5336546 : term305 = term305.
Proof. exact (eq_refl term305). Qed.
Lemma lem5336547 : term701 = term443.
Proof. exact (MK_COMB (@lem5336545) (@lem5336546)). Qed.
Lemma lem5336549 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336550 : term443 = term293.
Proof. exact (@lem5336549 term157). Qed.
Lemma lem5336551 : term701 = term293.
Proof. exact (TRANS (@lem5336547) (@lem5336550)). Qed.
Lemma lem5336553 (m : nat) (n : nat) : (term362 m n) = (term363 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5336554 : term364 = term365.
Proof. exact (@lem5336553 term157 term157). Qed.
Lemma lem5336555 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336556 : term367 = term157.
Proof. exact (EQ_MP (@lem5336555) (@lem940073)). Qed.
Lemma lem5336557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336558 : term365 = term305.
Proof. exact (MK_COMB (@lem5336557) (@lem5336556)). Qed.
Lemma lem5336559 : term364 = term305.
Proof. exact (TRANS (@lem5336554) (@lem5336558)). Qed.
Lemma lem5336560 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem5336561 : term445 = term443.
Proof. exact (MK_COMB (@lem5336560) (@lem5336559)). Qed.
Lemma lem5336563 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336564 : term443 = term293.
Proof. exact (@lem5336563 term157). Qed.
Lemma lem5336565 : term445 = term293.
Proof. exact (TRANS (@lem5336561) (@lem5336564)). Qed.
Lemma lem5336566 : term293 = term445.
Proof. exact (SYM (@lem5336565)). Qed.
Lemma lem5336567 : term701 = term445.
Proof. exact (TRANS (@lem5336551) (@lem5336566)). Qed.
Lemma lem5336568 : term692 = term352.
Proof. exact (@lem5336518 (@lem5336567)). Qed.
Lemma lem5336569 : term691 = term352.
Proof. exact (TRANS (@lem5336484) (@lem5336568)). Qed.
Lemma lem5336571 (x : real) : (term371 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5336572 : term352 = term293.
Proof. exact (@lem5336571 term293). Qed.
Lemma lem5336573 : term691 = term293.
Proof. exact (TRANS (@lem5336569) (@lem5336572)). Qed.
Lemma lem5336574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5336575 : term702 = term441.
Proof. exact (MK_COMB (@lem5336574) (@lem5336573)). Qed.
Lemma lem5336576 (_69707 : int) : (real_of_int _69707) = (real_of_int _69707).
Proof. exact (eq_refl (real_of_int _69707)). Qed.
Lemma lem5336577 (_69707 : int) : (term688 _69707) = (term703 _69707).
Proof. exact (MK_COMB (@lem5336575) (@lem5336576 _69707)). Qed.
Lemma lem5336578 (_69707 : int) : (term708 _69707) = (term703 _69707).
Proof. exact (TRANS (@lem5336475 _69707) (@lem5336577 _69707)). Qed.
Lemma lem5336579 (_69707 : int) : (term703 _69707) = term293.
Proof. exact (@lem1982719 (real_of_int _69707)). Qed.
Lemma lem5336580 (_69707 : int) : (term708 _69707) = term293.
Proof. exact (TRANS (@lem5336578 _69707) (@lem5336579 _69707)). Qed.
Lemma lem5336581 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5336582 (_69707 : int) : (term709 _69707) = term705.
Proof. exact (MK_COMB (@lem5336581) (@lem5336580 _69707)). Qed.
Lemma lem5336583 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem5336584 (_69707 : int) : (term707 _69707) = term710.
Proof. exact (MK_COMB (@lem5336582 _69707) (@lem5336583)). Qed.
Lemma lem5336585 (_69707 : int) : (term741 _69707) = term710.
Proof. exact (TRANS (@lem5336474 _69707) (@lem5336584 _69707)). Qed.
Lemma lem5336586 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5336587 (_69707 : int) : (term741 _69707) = term355.
Proof. exact (TRANS (@lem5336585 _69707) (@lem5336586)). Qed.
Lemma lem5336588 (_69705 : int) (_69707 : int) : (term739 _69705 _69707) = term710.
Proof. exact (MK_COMB (@lem5336473 _69705) (@lem5336587 _69707)). Qed.
Lemma lem5336589 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = term710.
Proof. exact (TRANS (@lem5336365 _69705 _69707) (@lem5336588 _69705 _69707)). Qed.
Lemma lem5336590 : term710 = term355.
Proof. exact (@lem1982721 term355). Qed.
Lemma lem5336591 (_69705 : int) (_69707 : int) : (term738 _69705 _69707) = term355.
Proof. exact (TRANS (@lem5336589 _69705 _69707) (@lem5336590)). Qed.
Lemma lem5336592 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5336593 (_69705 : int) (_69707 : int) : (term742 _69705 _69707) = term712.
Proof. exact (MK_COMB (@lem5336592) (@lem5336591 _69705 _69707)). Qed.
Lemma lem5336594 : term293 = term293.
Proof. exact (eq_refl term293). Qed.
Lemma lem5336595 (_69705 : int) (_69707 : int) : (term737 _69705 _69707) = term713.
Proof. exact (MK_COMB (@lem5336593 _69705 _69707) (@lem5336594)). Qed.
Lemma lem5336596 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : term713.
Proof. exact (EQ_MP (@lem5336595 _69705 _69707) (@lem5336364 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336598 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5336599 : term713 = term714.
Proof. exact (@lem5336598 term293 term355). Qed.
Lemma lem5336601 (x : nat) : (term353 x) = (term354 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5336602 : term355 = term356.
Proof. exact (@lem5336601 term157). Qed.
Lemma lem5336604 (x : nat) : (real_of_num x) = (term351 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5336605 : term293 = term352.
Proof. exact (@lem5336604 (NUMERAL 0)). Qed.
Lemma lem5336606 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5336607 : term295 = term715.
Proof. exact (MK_COMB (@lem5336606) (@lem5336605)). Qed.
Lemma lem5336608 : term714 = term716.
Proof. exact (MK_COMB (@lem5336607) (@lem5336602)). Qed.
Lemma lem5336609 : term717.
Proof. exact (@lem1980026 term293 term305 term355 term305). Qed.
Lemma lem5336611 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336612 : term431 = term432.
Proof. exact (@lem5336611 (NUMERAL 0) term157). Qed.
Lemma lem5336613 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336614 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336615 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336614 h1) (fun h1 : term432 = True => @lem5336613)). Qed.
Lemma lem5336616 : term432 = True.
Proof. exact (EQ_MP (@lem5336615) (@lem5336613)). Qed.
Lemma lem5336617 : term431 = True.
Proof. exact (TRANS (@lem5336612) (@lem5336616)). Qed.
Lemma lem5336618 : True = term431.
Proof. exact (SYM (@lem5336617)). Qed.
Lemma lem5336619 : term431.
Proof. exact (EQ_MP (@lem5336618) (@lem0)). Qed.
Lemma lem5336620 : term718.
Proof. exact (@lem5336609 (@lem5336619)). Qed.
Lemma lem5336622 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5336623 : term431 = term432.
Proof. exact (@lem5336622 (NUMERAL 0) term157). Qed.
Lemma lem5336624 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336625 (h1 : term433 = (BIT1 0)) : term432 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5336626 : (term433 = (BIT1 0)) = (term432 = True).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336625 h1) (fun h1 : term432 = True => @lem5336624)). Qed.
Lemma lem5336627 : term432 = True.
Proof. exact (EQ_MP (@lem5336626) (@lem5336624)). Qed.
Lemma lem5336628 : term431 = True.
Proof. exact (TRANS (@lem5336623) (@lem5336627)). Qed.
Lemma lem5336629 : True = term431.
Proof. exact (SYM (@lem5336628)). Qed.
Lemma lem5336630 : term431.
Proof. exact (EQ_MP (@lem5336629) (@lem0)). Qed.
Lemma lem5336631 : term716 = term719.
Proof. exact (@lem5336620 (@lem5336630)). Qed.
Lemma lem5336633 (m : nat) (n : nat) : (term401 m n) = (term402 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5336634 : term398 = term403.
Proof. exact (@lem5336633 term157 term157). Qed.
Lemma lem5336635 : (term366 = (BIT1 0)) = (term367 = term157).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5336636 : term367 = term157.
Proof. exact (EQ_MP (@lem5336635) (@lem940073)). Qed.
Lemma lem5336637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5336638 : term365 = term305.
Proof. exact (MK_COMB (@lem5336637) (@lem5336636)). Qed.
Lemma lem5336639 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5336640 : term403 = term355.
Proof. exact (MK_COMB (@lem5336639) (@lem5336638)). Qed.
Lemma lem5336641 : term398 = term355.
Proof. exact (TRANS (@lem5336634) (@lem5336640)). Qed.
Lemma lem5336643 (x : nat) : (term444 x) = term293.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5336644 : term443 = term293.
Proof. exact (@lem5336643 term157). Qed.
Lemma lem5336645 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5336646 : term720 = term295.
Proof. exact (MK_COMB (@lem5336645) (@lem5336644)). Qed.
Lemma lem5336647 : term719 = term714.
Proof. exact (MK_COMB (@lem5336646) (@lem5336641)). Qed.
Lemma lem5336649 (m : nat) (n : nat) : (term721 m n) = (term722 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5336650 : term714 = term723.
Proof. exact (@lem5336649 (NUMERAL 0) term157). Qed.
Lemma lem5336651 : term433 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5336652 (h1 : term433 = (BIT1 0)) : (term157 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5336653 : (term433 = (BIT1 0)) = ((term157 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term433 = (BIT1 0) => @lem5336652 h1) (fun h1 : (term157 = (NUMERAL 0)) = False => @lem5336651)). Qed.
Lemma lem5336654 : (term157 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5336653) (@lem5336651)). Qed.
Lemma lem5336655 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5336656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5336657 : term724 = (and True).
Proof. exact (MK_COMB (@lem5336656) (@lem5336655)). Qed.
Lemma lem5336658 : term723 = (True /\ False).
Proof. exact (MK_COMB (@lem5336657) (@lem5336654)). Qed.
Lemma lem5336660 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5336661 : term723 = False.
Proof. exact (TRANS (@lem5336658) (@lem5336660)). Qed.
Lemma lem5336662 : term714 = False.
Proof. exact (TRANS (@lem5336650) (@lem5336661)). Qed.
Lemma lem5336663 : term719 = False.
Proof. exact (TRANS (@lem5336647) (@lem5336662)). Qed.
Lemma lem5336664 : term716 = False.
Proof. exact (TRANS (@lem5336631) (@lem5336663)). Qed.
Lemma lem5336665 : term714 = False.
Proof. exact (TRANS (@lem5336608) (@lem5336664)). Qed.
Lemma lem5336666 : term713 = False.
Proof. exact (TRANS (@lem5336599) (@lem5336665)). Qed.
Lemma lem5336667 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term776 _69704 _69706 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5336666) (@lem5336596 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336668 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term635 _69704 _69706 _69705 _69707) : False.
Proof. exact (or_elim (@lem5335449 _69704 _69706 _69705 _69707 h1) (fun h0 : term767 _69704 _69706 _69705 _69707 => @lem5336194 _69704 _69706 _69705 _69707 h0) (fun h0 : term776 _69704 _69706 _69705 _69707 => @lem5336667 _69704 _69706 _69705 _69707 h0)). Qed.
Lemma lem5336669 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term644 _69704 _69706 _69705 _69707) : False.
Proof. exact (or_elim (@lem5334121 _69704 _69706 _69705 _69707 h1) (fun h0 : term639 _69706 _69705 _69704 _69707 => @lem5335448 _69706 _69705 _69704 _69707 h0) (fun h0 : term635 _69704 _69706 _69705 _69707 => @lem5336668 _69704 _69706 _69705 _69707 h0)). Qed.
Lemma lem5336670 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term660 _69704 _69706 _69705 _69707) : False.
Proof. exact (or_elim (@lem5332214 _69704 _69706 _69705 _69707 h1) (fun h0 : term657 _69706 _69704 _69705 _69707 => @lem5334120 _69706 _69704 _69705 _69707 h0) (fun h0 : term644 _69704 _69706 _69705 _69707 => @lem5336669 _69704 _69706 _69705 _69707 h0)). Qed.
Lemma lem5336672 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term660 _69704 _69706 _69705 _69707) : term660 _69704 _69706 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5336673 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term660 _69704 _69706 _69705 _69707) : (term660 _69704 _69706 _69705 _69707) = False.
Proof. exact (prop_ext (fun h2 : term660 _69704 _69706 _69705 _69707 => @lem5336670 _69704 _69706 _69705 _69707 h1) (fun h2 : False => @lem5336672 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336674 (_69704 : int) (_69706 : int) (_69705 : int) (_69707 : int) (h1 : term660 _69704 _69706 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5336673 _69704 _69706 _69705 _69707 h1) (@lem5336672 _69704 _69706 _69705 _69707 h1)). Qed.
Lemma lem5336675 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term347 _69706 _69704 _69705 _69707) : term347 _69706 _69704 _69705 _69707.
Proof. exact (h1). Qed.
Lemma lem5336676 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term347 _69706 _69704 _69705 _69707) : term660 _69704 _69706 _69705 _69707.
Proof. exact (EQ_MP (@lem5332168 _69704 _69706 _69705 _69707) (@lem5336675 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5336677 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term347 _69706 _69704 _69705 _69707) : (term660 _69704 _69706 _69705 _69707) = False.
Proof. exact (prop_ext (fun h2 : term660 _69704 _69706 _69705 _69707 => @lem5336674 _69704 _69706 _69705 _69707 h2) (fun h2 : False => @lem5336676 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5336678 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) (h1 : term347 _69706 _69704 _69705 _69707) : False.
Proof. exact (EQ_MP (@lem5336677 _69706 _69704 _69705 _69707 h1) (@lem5336676 _69706 _69704 _69705 _69707 h1)). Qed.
Lemma lem5336679 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : term777 _69706 _69704 _69705 _69707.
Proof. exact (fun h0 : term347 _69706 _69704 _69705 _69707 => @lem5336678 _69706 _69704 _69705 _69707 h0). Qed.
Lemma lem5336680 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : term778 _69706 _69704 _69705 _69707.
Proof. exact (@lem1386578 (term779 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5336683 (_69706 : int) (_69704 : int) (_69705 : int) (_69707 : int) : term779 _69706 _69704 _69705 _69707.
Proof. exact (@lem5336680 _69706 _69704 _69705 _69707 (@lem5336679 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5336684 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term345 _69706 _69704 _69705 _69707) = (term286 _69706 _69704 _69707 _69705).
Proof. exact (SYM (@lem5330643 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5336685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5336686 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : (term779 _69706 _69704 _69705 _69707) = (term207 _69706 _69704 _69707 _69705).
Proof. exact (MK_COMB (@lem5336685) (@lem5336684 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5336687 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : term207 _69706 _69704 _69707 _69705.
Proof. exact (EQ_MP (@lem5336686 _69706 _69704 _69707 _69705) (@lem5336683 _69706 _69704 _69705 _69707)). Qed.
Lemma lem5336688 (_69706 : int) (_69704 : int) (_69707 : int) (_69705 : int) : term208 _69706 _69704 _69707 _69705.
Proof. exact (EQ_MP (@lem5330098 _69706 _69704 _69707 _69705) (@lem5336687 _69706 _69704 _69707 _69705)). Qed.
Lemma lem5336689 (p : nat) (m : nat) (x : nat) (n : nat) : term780 p m x n.
Proof. exact (@lem5336688 (int_of_num p) (int_of_num m) (int_of_num x) (int_of_num n)). Qed.
Lemma lem5336690 (p : nat) (m : nat) (x : nat) (n : nat) : term781 p m x n.
Proof. exact (@lem5336689 p m x n (@lem5330088 m)). Qed.
Lemma lem5336691 (p : nat) (m : nat) (x : nat) (n : nat) : term782 p m x n.
Proof. exact (@lem5336690 p m x n (@lem5330091 n)). Qed.
Lemma lem5336692 (p : nat) (m : nat) (x : nat) (n : nat) : term783 p m x n.
Proof. exact (@lem5336691 p m x n (@lem5330094 p)). Qed.
Lemma lem5336693 (p : nat) (m : nat) (x : nat) (n : nat) : term196 p m x n.
Proof. exact (@lem5336692 p m x n (@lem5330097 x)). Qed.
Lemma lem5336694 (p : nat) (m : nat) (n : nat) : term198 p m n.
Proof. exact (fun x : nat => @lem5336693 p m x n). Qed.
Lemma lem5336695 (p : nat) (m : nat) : term200 p m.
Proof. exact (fun n : nat => @lem5336694 p m n). Qed.
Lemma lem5336696 (m : nat) : term202 m.
Proof. exact (fun p : nat => @lem5336695 p m). Qed.
Lemma lem5336697 : term204.
Proof. exact (fun m : nat => @lem5336696 m). Qed.
Lemma lem5336698 : term204 = term91.
Proof. exact (SYM (@lem5330085)). Qed.
Lemma lem5336699 : term91.
Proof. exact (EQ_MP (@lem5336698) (@lem5336697)). Qed.
Lemma lem5336700 : term91 = (term91 = True).
Proof. exact (@lem7 term91). Qed.
Lemma lem5336701 : term91 = True.
Proof. exact (EQ_MP (@lem5336700) (@lem5336699)). Qed.
Lemma lem5336702 : True = term91.
Proof. exact (SYM (@lem5336701)). Qed.
Lemma lem5336703 : term91.
Proof. exact (EQ_MP (@lem5336702) (@lem0)). Qed.
Lemma lem5336704 : term90.
Proof. exact (EQ_MP (@lem5329548) (@lem5336703)). Qed.
