Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LSQRT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import POW_2_SQRT_spec.
Require Import REAL_POW_LE_spec.
Require Import SQRT_MONO_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1957859 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1957860 : term1 = term2.
Proof. exact (@lem1957859 term1). Qed.
Lemma lem1957861 : term2 = term1.
Proof. exact (SYM (@lem1957860)). Qed.
Lemma lem1957862 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1957865 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1957866 : term5.
Proof. exact (fun h0 : term4 => @lem1957865 h0). Qed.
Lemma lem1957867 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1957868 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1957869 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1957867 h2 (@lem1957868 h1)). Qed.
Lemma lem1957870 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1957869 h1 h0). Qed.
Lemma lem1957871 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1957872 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1957870 h1 (@lem1957871 h2)). Qed.
Lemma lem1957873 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1957872 h0 h1). Qed.
Lemma lem1957874 : term7.
Proof. exact (fun h0 : term5 => @lem1957873 h0). Qed.
Lemma lem1957877 : term5.
Proof. exact (@lem1957874 (@lem1957866)). Qed.
Lemma lem1957913 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1957914 : term8 = term9.
Proof. exact (@lem1957913 term10). Qed.
Lemma lem1957925 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1957926 : term12 = term13.
Proof. exact (MK_COMB (@lem1957925) (@lem1957914)). Qed.
Lemma lem1957929 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1957930 : term15 = term16.
Proof. exact (MK_COMB (@lem1957929) (@lem1957926)). Qed.
Lemma lem1957933 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1957940 : term4 = term18.
Proof. exact (MK_COMB (@lem1957933) (@lem1957930)). Qed.
Lemma lem1957945 (x : real) (y : real) : (term19 x y) = (term19 x y).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1957946 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1957945 x y)). Qed.
Lemma lem1957947 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957948 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1957947) (@lem1957946 x)). Qed.
Lemma lem1957949 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1957948 x)). Qed.
Lemma lem1957950 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957951 : term10 = term10.
Proof. exact (MK_COMB (@lem1957950) (@lem1957949)). Qed.
Lemma lem1957952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1957953 : term9 = term9.
Proof. exact (MK_COMB (@lem1957952) (@lem1957951)). Qed.
Lemma lem1957958 (x : real) (n : nat) : (term23 x n) = (term23 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1957959 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun n : nat => @lem1957958 x n)). Qed.
Lemma lem1957960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1957961 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1957960) (@lem1957959 x)). Qed.
Lemma lem1957962 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1957961 x)). Qed.
Lemma lem1957963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957964 : term27 = term27.
Proof. exact (MK_COMB (@lem1957963) (@lem1957962)). Qed.
Lemma lem1957965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957966 : term11 = term11.
Proof. exact (MK_COMB (@lem1957965) (@lem1957964)). Qed.
Lemma lem1957967 : term13 = term13.
Proof. exact (MK_COMB (@lem1957966) (@lem1957953)). Qed.
Lemma lem1957972 (x : real) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1957973 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1957972 x)). Qed.
Lemma lem1957974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957975 : term30 = term30.
Proof. exact (MK_COMB (@lem1957974) (@lem1957973)). Qed.
Lemma lem1957976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957977 : term14 = term14.
Proof. exact (MK_COMB (@lem1957976) (@lem1957975)). Qed.
Lemma lem1957978 : term16 = term16.
Proof. exact (MK_COMB (@lem1957977) (@lem1957967)). Qed.
Lemma lem1957987 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1957988 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1957987 x y)). Qed.
Lemma lem1957989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957990 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1957989) (@lem1957988 x)). Qed.
Lemma lem1957991 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1957990 x)). Qed.
Lemma lem1957992 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957993 : term1 = term1.
Proof. exact (MK_COMB (@lem1957992) (@lem1957991)). Qed.
Lemma lem1957994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1957995 : term3 = term3.
Proof. exact (MK_COMB (@lem1957994) (@lem1957993)). Qed.
Lemma lem1957996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957997 : term17 = term17.
Proof. exact (MK_COMB (@lem1957996) (@lem1957995)). Qed.
Lemma lem1957998 : term18 = term18.
Proof. exact (MK_COMB (@lem1957997) (@lem1957978)). Qed.
Lemma lem1958059 : term4 = term18.
Proof. exact (TRANS (@lem1957940) (@lem1957998)). Qed.
Lemma lem1958060 : term18 = term4.
Proof. exact (SYM (@lem1958059)). Qed.
Lemma lem1958061 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1958062 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1958064 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1958075 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem17362 (term37 x y) (term38 x y)). Qed.
Lemma lem1958076 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1958077 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1958076 (term32 x)). Qed.
Lemma lem1958078 (x : real) (y : real) : (term43 x y) = (term31 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1958079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1958080 (x : real) (y : real) : (term44 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1958079) (@lem1958078 x y)). Qed.
Lemma lem1958081 (x : real) (y : real) : (term44 x y) = (term36 x y).
Proof. exact (TRANS (@lem1958080 x y) (@lem1958075 x y)). Qed.
Lemma lem1958082 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1958081 x y)). Qed.
Lemma lem1958083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1958084 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1958083) (@lem1958082 x)). Qed.
Lemma lem1958085 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1958077 x) (@lem1958084 x)). Qed.
Lemma lem1958086 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1958087 : term3 = term48.
Proof. exact (@lem1958086 term34). Qed.
Lemma lem1958088 (x : real) : (term49 x) = (term33 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1958089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1958090 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1958089) (@lem1958088 x)). Qed.
Lemma lem1958091 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1958090 x) (@lem1958085 x)). Qed.
Lemma lem1958092 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1958091 x)). Qed.
Lemma lem1958093 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1958094 : term48 = term53.
Proof. exact (MK_COMB (@lem1958093) (@lem1958092)). Qed.
Lemma lem1958151 : term3 = term53.
Proof. exact (TRANS (@lem1958087) (@lem1958094)). Qed.
Lemma lem1958152 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem1958151) (@lem1958061 h1)). Qed.
Lemma lem1958159 (x : real) : (term28 x) = (term54 x).
Proof. exact (@lem17265 (term55 x) ((term56 x) = x)). Qed.
Lemma lem1958160 : term29 = term57.
Proof. exact (fun_ext (fun x : real => @lem1958159 x)). Qed.
Lemma lem1958161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958214 : term30 = term58.
Proof. exact (MK_COMB (@lem1958161) (@lem1958160)). Qed.
Lemma lem1958215 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1958214) (@lem1958062 h1)). Qed.
Lemma lem1958318 (x : real) (y : real) : (term19 x y) = (term59 x y).
Proof. exact (@lem17265 (real_le x y) (term60 x y)). Qed.
Lemma lem1958319 (x : real) : (term20 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1958318 x y)). Qed.
Lemma lem1958320 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958321 (x : real) : (term21 x) = (term62 x).
Proof. exact (MK_COMB (@lem1958320) (@lem1958319 x)). Qed.
Lemma lem1958322 : term22 = term63.
Proof. exact (fun_ext (fun x : real => @lem1958321 x)). Qed.
Lemma lem1958323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958380 : term10 = term64.
Proof. exact (MK_COMB (@lem1958323) (@lem1958322)). Qed.
Lemma lem1958381 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1958380) (@lem1958064 h1)). Qed.
Lemma lem1958382 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1958414 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1958415 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1958414 x)). Qed.
Lemma lem1958416 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958417 : term58 = term58.
Proof. exact (MK_COMB (@lem1958416) (@lem1958415)). Qed.
Lemma lem1958418 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1958417) (@lem1958215 h1)). Qed.
Lemma lem1958471 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1958472 (x : real) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1958471 x y)). Qed.
Lemma lem1958473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958474 (x : real) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem1958473) (@lem1958472 x)). Qed.
Lemma lem1958475 : term63 = term63.
Proof. exact (fun_ext (fun x : real => @lem1958474 x)). Qed.
Lemma lem1958476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958477 : term64 = term64.
Proof. exact (MK_COMB (@lem1958476) (@lem1958475)). Qed.
Lemma lem1958478 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1958477) (@lem1958381 h1)). Qed.
Lemma lem1958518 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1958520 (x : real) (y : real) (h1 : term36 x y) : term37 x y.
Proof. exact (proj1 (@lem1958518 x y h1)). Qed.
Lemma lem1958530 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1958531 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1958530 x)). Qed.
Lemma lem1958532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958534 : term58 = term58.
Proof. exact (MK_COMB (@lem1958532) (@lem1958531)). Qed.
Lemma lem1958535 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1958534) (@lem1958418 h1)). Qed.
Lemma lem1958581 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1958582 (x : real) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1958581 x y)). Qed.
Lemma lem1958583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958584 (x : real) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem1958583) (@lem1958582 x)). Qed.
Lemma lem1958585 : term63 = term63.
Proof. exact (fun_ext (fun x : real => @lem1958584 x)). Qed.
Lemma lem1958586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1958588 : term64 = term64.
Proof. exact (MK_COMB (@lem1958586) (@lem1958585)). Qed.
Lemma lem1958589 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1958588) (@lem1958478 h1)). Qed.
Lemma lem1958602 (_27481 : real) (h1 : term30) : term65 _27481.
Proof. exact (@lem1958535 h1 _27481). Qed.
Lemma lem1958603 (_27481 : real) : (term65 _27481) = (term54 _27481).
Proof. exact (eq_refl (term65 _27481)). Qed.
Lemma lem1958611 (_27484 : real) (h1 : term10) : term66 _27484.
Proof. exact (@lem1958589 h1 _27484). Qed.
Lemma lem1958612 (_27484 : real) : (term66 _27484) = (term62 _27484).
Proof. exact (eq_refl (term66 _27484)). Qed.
Lemma lem1958613 (_27484 : real) (h1 : term10) : term62 _27484.
Proof. exact (EQ_MP (@lem1958612 _27484) (@lem1958611 _27484 h1)). Qed.
Lemma lem1958614 (_27484 : real) (_27485 : real) (h1 : term10) : term67 _27484 _27485.
Proof. exact (@lem1958613 _27484 h1 _27485). Qed.
Lemma lem1958615 (_27484 : real) (_27485 : real) : (term67 _27484 _27485) = (term59 _27484 _27485).
Proof. exact (eq_refl (term67 _27484 _27485)). Qed.
Lemma lem1958622 (_27481 : real) (h1 : term30) : term54 _27481.
Proof. exact (EQ_MP (@lem1958603 _27481) (@lem1958602 _27481 h1)). Qed.
Lemma lem1958634 (_27484 : real) (_27485 : real) (h1 : term10) : term59 _27484 _27485.
Proof. exact (EQ_MP (@lem1958615 _27484 _27485) (@lem1958614 _27484 _27485 h1)). Qed.
Lemma lem1958636 (x : real) (y : real) (h1 : term36 x y) : term68 x y.
Proof. exact (proj2 (@lem1958518 x y h1)). Qed.
Lemma lem1958641 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1958642 (_27486 : real) (_27488 : real) (h1 : _27486 = _27488) : _27486 = _27488.
Proof. exact (h1). Qed.
Lemma lem1958643 (_27487 : real) (_27489 : real) (h1 : _27487 = _27489) : _27487 = _27489.
Proof. exact (h1). Qed.
Lemma lem1958644 (_27486 : real) (_27488 : real) (h1 : _27486 = _27488) : (real_le _27486) = (real_le _27488).
Proof. exact (MK_COMB (@lem1958641) (@lem1958642 _27486 _27488 h1)). Qed.
Lemma lem1958645 (_27486 : real) (_27488 : real) (_27487 : real) (_27489 : real) (h1 : _27486 = _27488) (h2 : _27487 = _27489) : (real_le _27486 _27487) = (real_le _27488 _27489).
Proof. exact (MK_COMB (@lem1958644 _27486 _27488 h1) (@lem1958643 _27487 _27489 h2)). Qed.
Lemma lem1958647 (b : Prop) (a : Prop) : term69 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1958648 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : term70 _27488 _27489 _27486 _27487.
Proof. exact (@lem1958647 (real_le _27488 _27489) (real_le _27486 _27487)). Qed.
Lemma lem1958649 (_27486 : real) (_27488 : real) (_27487 : real) (_27489 : real) (h1 : _27486 = _27488) (h2 : _27487 = _27489) : term71 _27488 _27489 _27486 _27487.
Proof. exact (@lem1958648 _27488 _27489 _27486 _27487 (@lem1958645 _27486 _27488 _27487 _27489 h1 h2)). Qed.
Lemma lem1958650 (_27489 : real) (_27487 : real) (_27486 : real) (_27488 : real) (h1 : _27486 = _27488) : term72 _27488 _27489 _27486 _27487.
Proof. exact (fun h0 : _27487 = _27489 => @lem1958649 _27486 _27488 _27487 _27489 h1 h0). Qed.
Lemma lem1958652 (a : Prop) (b : Prop) : (a -> b) = (term73 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1958653 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term72 _27488 _27489 _27486 _27487) = (term74 _27488 _27489 _27486 _27487).
Proof. exact (@lem1958652 (_27487 = _27489) (term71 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958654 (_27489 : real) (_27487 : real) (_27486 : real) (_27488 : real) (h1 : _27486 = _27488) : term74 _27488 _27489 _27486 _27487.
Proof. exact (EQ_MP (@lem1958653 _27488 _27489 _27486 _27487) (@lem1958650 _27489 _27487 _27486 _27488 h1)). Qed.
Lemma lem1958655 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : term75 _27488 _27489 _27486 _27487.
Proof. exact (fun h0 : _27486 = _27488 => @lem1958654 _27489 _27487 _27486 _27488 h0). Qed.
Lemma lem1958657 (a : Prop) (b : Prop) : (a -> b) = (term73 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1958658 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term75 _27488 _27489 _27486 _27487) = (term76 _27488 _27489 _27486 _27487).
Proof. exact (@lem1958657 (_27486 = _27488) (term74 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958659 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : term76 _27488 _27489 _27486 _27487.
Proof. exact (EQ_MP (@lem1958658 _27488 _27489 _27486 _27487) (@lem1958655 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958720 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1958721 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (@lem1958720 (sqrt x)). Qed.
Lemma lem1958722 (x : real) : term77 x.
Proof. exact (fun h0 : term78 x => @lem1958721 x). Qed.
Lemma lem1958724 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1958725 (x : real) : (term77 x) = ((sqrt x) = (sqrt x)).
Proof. exact (@lem1958724 ((sqrt x) = (sqrt x))). Qed.
Lemma lem1958726 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (EQ_MP (@lem1958725 x) (@lem1958722 x)). Qed.
Lemma lem1958728 (x : real) (y : real) (h1 : term36 x y) : term55 y.
Proof. exact (proj1 (@lem1958520 x y h1)). Qed.
Lemma lem1958729 (x : real) (y : real) (h1 : term36 x y) : term80 y.
Proof. exact (fun h0 : term81 y => @lem1958728 x y h1). Qed.
Lemma lem1958731 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1958732 (y : real) : (term80 y) = (term55 y).
Proof. exact (@lem1958731 (term55 y)). Qed.
Lemma lem1958733 (x : real) (y : real) (h1 : term36 x y) : term55 y.
Proof. exact (EQ_MP (@lem1958732 y) (@lem1958729 x y h1)). Qed.
Lemma lem1958739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1958740 (_27481 : real) : (term54 _27481) = (term82 _27481).
Proof. exact (@lem1958739 ((term56 _27481) = _27481) (term81 _27481)). Qed.
Lemma lem1958748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1958749 (_27481 : real) : (term83 _27481) = (term84 _27481).
Proof. exact (MK_COMB (@lem1958748) (@lem1958740 _27481)). Qed.
Lemma lem1958757 (_27481 : real) : (term82 _27481) = (term82 _27481).
Proof. exact (eq_refl (term82 _27481)). Qed.
Lemma lem1958758 (_27481 : real) : ((term54 _27481) = (term82 _27481)) = ((term82 _27481) = (term82 _27481)).
Proof. exact (MK_COMB (@lem1958749 _27481) (@lem1958757 _27481)). Qed.
Lemma lem1958760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1958761 (x : Prop) : (x = x) = True.
Proof. exact (@lem1958760 Prop x). Qed.
Lemma lem1958762 (_27481 : real) : ((term82 _27481) = (term82 _27481)) = True.
Proof. exact (@lem1958761 (term82 _27481)). Qed.
Lemma lem1958763 (_27481 : real) : ((term54 _27481) = (term82 _27481)) = True.
Proof. exact (TRANS (@lem1958758 _27481) (@lem1958762 _27481)). Qed.
Lemma lem1958764 (_27481 : real) : True = ((term54 _27481) = (term82 _27481)).
Proof. exact (SYM (@lem1958763 _27481)). Qed.
Lemma lem1958765 (_27481 : real) : (term54 _27481) = (term82 _27481).
Proof. exact (EQ_MP (@lem1958764 _27481) (@lem0)). Qed.
Lemma lem1958766 (_27481 : real) (h1 : term30) : term82 _27481.
Proof. exact (EQ_MP (@lem1958765 _27481) (@lem1958622 _27481 h1)). Qed.
Lemma lem1958768 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1958769 (_27481 : real) : (term82 _27481) = (term86 _27481).
Proof. exact (@lem1958768 (term81 _27481) ((term56 _27481) = _27481)). Qed.
Lemma lem1958771 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1958772 (_27481 : real) : (term88 _27481) = (term55 _27481).
Proof. exact (@lem1958771 (term55 _27481)). Qed.
Lemma lem1958773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1958774 (_27481 : real) : (term89 _27481) = (term90 _27481).
Proof. exact (MK_COMB (@lem1958773) (@lem1958772 _27481)). Qed.
Lemma lem1958775 (_27481 : real) : ((term56 _27481) = _27481) = ((term56 _27481) = _27481).
Proof. exact (eq_refl ((term56 _27481) = _27481)). Qed.
Lemma lem1958776 (_27481 : real) : (term86 _27481) = (term28 _27481).
Proof. exact (MK_COMB (@lem1958774 _27481) (@lem1958775 _27481)). Qed.
Lemma lem1958777 (_27481 : real) : (term82 _27481) = (term28 _27481).
Proof. exact (TRANS (@lem1958769 _27481) (@lem1958776 _27481)). Qed.
Lemma lem1958780 (_27481 : real) (h1 : term30) : term28 _27481.
Proof. exact (EQ_MP (@lem1958777 _27481) (@lem1958766 _27481 h1)). Qed.
Lemma lem1958781 (y : real) (h1 : term30) : term28 y.
Proof. exact (@lem1958780 y h1). Qed.
Lemma lem1958784 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : (term56 y) = y.
Proof. exact (@lem1958781 y h1 (@lem1958733 x y h2)). Qed.
Lemma lem1958785 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : term91 y.
Proof. exact (fun h0 : term92 y => @lem1958784 x y h1 h2). Qed.
Lemma lem1958787 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1958788 (y : real) : (term91 y) = ((term56 y) = y).
Proof. exact (@lem1958787 ((term56 y) = y)). Qed.
Lemma lem1958789 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : (term56 y) = y.
Proof. exact (EQ_MP (@lem1958788 y) (@lem1958785 x y h1 h2)). Qed.
Lemma lem1958791 (x : real) (y : real) (h1 : term36 x y) : term93 x y.
Proof. exact (proj2 (@lem1958520 x y h1)). Qed.
Lemma lem1958792 (x : real) (y : real) (h1 : term36 x y) : term94 x y.
Proof. exact (fun h0 : term95 x y => @lem1958791 x y h1). Qed.
Lemma lem1958794 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1958795 (x : real) (y : real) : (term94 x y) = (term93 x y).
Proof. exact (@lem1958794 (term93 x y)). Qed.
Lemma lem1958796 (x : real) (y : real) (h1 : term36 x y) : term93 x y.
Proof. exact (EQ_MP (@lem1958795 x y) (@lem1958792 x y h1)). Qed.
Lemma lem1958802 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1958803 (_27484 : real) (_27485 : real) : (term59 _27484 _27485) = (term96 _27484 _27485).
Proof. exact (@lem1958802 (term60 _27484 _27485) (term97 _27484 _27485)). Qed.
Lemma lem1958809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1958810 (_27484 : real) (_27485 : real) : (term98 _27484 _27485) = (term99 _27484 _27485).
Proof. exact (MK_COMB (@lem1958809) (@lem1958803 _27484 _27485)). Qed.
Lemma lem1958816 (_27484 : real) (_27485 : real) : (term96 _27484 _27485) = (term96 _27484 _27485).
Proof. exact (eq_refl (term96 _27484 _27485)). Qed.
Lemma lem1958817 (_27484 : real) (_27485 : real) : ((term59 _27484 _27485) = (term96 _27484 _27485)) = ((term96 _27484 _27485) = (term96 _27484 _27485)).
Proof. exact (MK_COMB (@lem1958810 _27484 _27485) (@lem1958816 _27484 _27485)). Qed.
Lemma lem1958819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1958820 (x : Prop) : (x = x) = True.
Proof. exact (@lem1958819 Prop x). Qed.
Lemma lem1958821 (_27484 : real) (_27485 : real) : ((term96 _27484 _27485) = (term96 _27484 _27485)) = True.
Proof. exact (@lem1958820 (term96 _27484 _27485)). Qed.
Lemma lem1958822 (_27484 : real) (_27485 : real) : ((term59 _27484 _27485) = (term96 _27484 _27485)) = True.
Proof. exact (TRANS (@lem1958817 _27484 _27485) (@lem1958821 _27484 _27485)). Qed.
Lemma lem1958823 (_27484 : real) (_27485 : real) : True = ((term59 _27484 _27485) = (term96 _27484 _27485)).
Proof. exact (SYM (@lem1958822 _27484 _27485)). Qed.
Lemma lem1958824 (_27484 : real) (_27485 : real) : (term59 _27484 _27485) = (term96 _27484 _27485).
Proof. exact (EQ_MP (@lem1958823 _27484 _27485) (@lem0)). Qed.
Lemma lem1958825 (_27484 : real) (_27485 : real) (h1 : term10) : term96 _27484 _27485.
Proof. exact (EQ_MP (@lem1958824 _27484 _27485) (@lem1958634 _27484 _27485 h1)). Qed.
Lemma lem1958827 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1958828 (_27484 : real) (_27485 : real) : (term96 _27484 _27485) = (term100 _27484 _27485).
Proof. exact (@lem1958827 (term97 _27484 _27485) (term60 _27484 _27485)). Qed.
Lemma lem1958830 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1958831 (_27484 : real) (_27485 : real) : (term101 _27484 _27485) = (real_le _27484 _27485).
Proof. exact (@lem1958830 (real_le _27484 _27485)). Qed.
Lemma lem1958832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1958833 (_27484 : real) (_27485 : real) : (term102 _27484 _27485) = (term103 _27484 _27485).
Proof. exact (MK_COMB (@lem1958832) (@lem1958831 _27484 _27485)). Qed.
Lemma lem1958834 (_27484 : real) (_27485 : real) : (term60 _27484 _27485) = (term60 _27484 _27485).
Proof. exact (eq_refl (term60 _27484 _27485)). Qed.
Lemma lem1958835 (_27484 : real) (_27485 : real) : (term100 _27484 _27485) = (term19 _27484 _27485).
Proof. exact (MK_COMB (@lem1958833 _27484 _27485) (@lem1958834 _27484 _27485)). Qed.
Lemma lem1958836 (_27484 : real) (_27485 : real) : (term96 _27484 _27485) = (term19 _27484 _27485).
Proof. exact (TRANS (@lem1958828 _27484 _27485) (@lem1958835 _27484 _27485)). Qed.
Lemma lem1958839 (_27484 : real) (_27485 : real) (h1 : term10) : term19 _27484 _27485.
Proof. exact (EQ_MP (@lem1958836 _27484 _27485) (@lem1958825 _27484 _27485 h1)). Qed.
Lemma lem1958840 (x : real) (y : real) (h1 : term10) : term104 x y.
Proof. exact (@lem1958839 x (term105 y) h1). Qed.
Lemma lem1958843 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term106 x y.
Proof. exact (@lem1958840 x y h1 (@lem1958796 x y h2)). Qed.
Lemma lem1958844 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term107 x y.
Proof. exact (fun h0 : term108 x y => @lem1958843 x y h1 h2). Qed.
Lemma lem1958846 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1958847 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1958846 (term106 x y)). Qed.
Lemma lem1958848 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1958847 x y) (@lem1958844 x y h1 h2)). Qed.
Lemma lem1958866 (q : Prop) (p : Prop) (r : Prop) : (term109 p q r) = (term109 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1958867 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term74 _27488 _27489 _27486 _27487) = (term110 _27488 _27489 _27486 _27487).
Proof. exact (@lem1958866 (real_le _27488 _27489) (term111 _27487 _27489) (term97 _27486 _27487)). Qed.
Lemma lem1958885 (_27486 : real) (_27488 : real) : (term112 _27486 _27488) = (term112 _27486 _27488).
Proof. exact (eq_refl (term112 _27486 _27488)). Qed.
Lemma lem1958886 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term76 _27488 _27489 _27486 _27487) = (term113 _27488 _27489 _27486 _27487).
Proof. exact (MK_COMB (@lem1958885 _27486 _27488) (@lem1958867 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958890 (q : Prop) (p : Prop) (r : Prop) : (term109 p q r) = (term109 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1958891 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term113 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487).
Proof. exact (@lem1958890 (real_le _27488 _27489) (term111 _27486 _27488) (term115 _27489 _27486 _27487)). Qed.
Lemma lem1958921 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term76 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487).
Proof. exact (TRANS (@lem1958886 _27488 _27489 _27486 _27487) (@lem1958891 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1958923 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term116 _27488 _27489 _27486 _27487) = (term117 _27488 _27489 _27486 _27487).
Proof. exact (MK_COMB (@lem1958922) (@lem1958921 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958953 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term114 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487).
Proof. exact (eq_refl (term114 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958954 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : ((term76 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487)) = ((term114 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487)).
Proof. exact (MK_COMB (@lem1958923 _27488 _27489 _27486 _27487) (@lem1958953 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1958957 (x : Prop) : (x = x) = True.
Proof. exact (@lem1958956 Prop x). Qed.
Lemma lem1958958 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : ((term114 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487)) = True.
Proof. exact (@lem1958957 (term114 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958959 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : ((term76 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487)) = True.
Proof. exact (TRANS (@lem1958954 _27488 _27489 _27486 _27487) (@lem1958958 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958960 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : True = ((term76 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487)).
Proof. exact (SYM (@lem1958959 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958961 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term76 _27488 _27489 _27486 _27487) = (term114 _27488 _27489 _27486 _27487).
Proof. exact (EQ_MP (@lem1958960 _27488 _27489 _27486 _27487) (@lem0)). Qed.
Lemma lem1958962 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : term114 _27488 _27489 _27486 _27487.
Proof. exact (EQ_MP (@lem1958961 _27488 _27489 _27486 _27487) (@lem1958659 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958964 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1958965 (_27486 : real) (_27487 : real) (_27488 : real) (_27489 : real) : (term114 _27488 _27489 _27486 _27487) = (term118 _27486 _27487 _27488 _27489).
Proof. exact (@lem1958964 (term119 _27488 _27489 _27486 _27487) (real_le _27488 _27489)). Qed.
Lemma lem1958967 (a : Prop) (b : Prop) : (term120 a b) = (term121 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1958968 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term122 _27488 _27489 _27486 _27487) = (term123 _27488 _27489 _27486 _27487).
Proof. exact (@lem1958967 (term111 _27486 _27488) (term115 _27489 _27486 _27487)). Qed.
Lemma lem1958970 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1958971 (_27486 : real) (_27488 : real) : (term124 _27486 _27488) = (_27486 = _27488).
Proof. exact (@lem1958970 (_27486 = _27488)). Qed.
Lemma lem1958972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1958973 (_27486 : real) (_27488 : real) : (term125 _27486 _27488) = (term126 _27486 _27488).
Proof. exact (MK_COMB (@lem1958972) (@lem1958971 _27486 _27488)). Qed.
Lemma lem1958975 (a : Prop) (b : Prop) : (term120 a b) = (term121 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1958976 (_27489 : real) (_27486 : real) (_27487 : real) : (term127 _27489 _27486 _27487) = (term128 _27489 _27486 _27487).
Proof. exact (@lem1958975 (term111 _27487 _27489) (term97 _27486 _27487)). Qed.
Lemma lem1958978 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1958979 (_27487 : real) (_27489 : real) : (term124 _27487 _27489) = (_27487 = _27489).
Proof. exact (@lem1958978 (_27487 = _27489)). Qed.
Lemma lem1958980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1958981 (_27487 : real) (_27489 : real) : (term125 _27487 _27489) = (term126 _27487 _27489).
Proof. exact (MK_COMB (@lem1958980) (@lem1958979 _27487 _27489)). Qed.
Lemma lem1958983 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1958984 (_27486 : real) (_27487 : real) : (term101 _27486 _27487) = (real_le _27486 _27487).
Proof. exact (@lem1958983 (real_le _27486 _27487)). Qed.
Lemma lem1958985 (_27489 : real) (_27486 : real) (_27487 : real) : (term128 _27489 _27486 _27487) = (term129 _27489 _27486 _27487).
Proof. exact (MK_COMB (@lem1958981 _27487 _27489) (@lem1958984 _27486 _27487)). Qed.
Lemma lem1958986 (_27489 : real) (_27486 : real) (_27487 : real) : (term127 _27489 _27486 _27487) = (term129 _27489 _27486 _27487).
Proof. exact (TRANS (@lem1958976 _27489 _27486 _27487) (@lem1958985 _27489 _27486 _27487)). Qed.
Lemma lem1958987 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term123 _27488 _27489 _27486 _27487) = (term130 _27488 _27489 _27486 _27487).
Proof. exact (MK_COMB (@lem1958973 _27486 _27488) (@lem1958986 _27489 _27486 _27487)). Qed.
Lemma lem1958988 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term122 _27488 _27489 _27486 _27487) = (term130 _27488 _27489 _27486 _27487).
Proof. exact (TRANS (@lem1958968 _27488 _27489 _27486 _27487) (@lem1958987 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1958990 (_27488 : real) (_27489 : real) (_27486 : real) (_27487 : real) : (term131 _27488 _27489 _27486 _27487) = (term132 _27488 _27489 _27486 _27487).
Proof. exact (MK_COMB (@lem1958989) (@lem1958988 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958991 (_27488 : real) (_27489 : real) : (real_le _27488 _27489) = (real_le _27488 _27489).
Proof. exact (eq_refl (real_le _27488 _27489)). Qed.
Lemma lem1958992 (_27486 : real) (_27487 : real) (_27488 : real) (_27489 : real) : (term118 _27486 _27487 _27488 _27489) = (term133 _27486 _27487 _27488 _27489).
Proof. exact (MK_COMB (@lem1958990 _27488 _27489 _27486 _27487) (@lem1958991 _27488 _27489)). Qed.
Lemma lem1958993 (_27486 : real) (_27487 : real) (_27488 : real) (_27489 : real) : (term114 _27488 _27489 _27486 _27487) = (term133 _27486 _27487 _27488 _27489).
Proof. exact (TRANS (@lem1958965 _27486 _27487 _27488 _27489) (@lem1958992 _27486 _27487 _27488 _27489)). Qed.
Lemma lem1958995 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term134 x y.
Proof. exact (conj (@lem1958789 x y h2 h3) (@lem1958848 x y h1 h3)). Qed.
Lemma lem1958996 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term135 x y.
Proof. exact (conj (@lem1958726 x) (@lem1958995 x y h1 h2 h3)). Qed.
Lemma lem1958998 (_27486 : real) (_27487 : real) (_27488 : real) (_27489 : real) : term133 _27486 _27487 _27488 _27489.
Proof. exact (EQ_MP (@lem1958993 _27486 _27487 _27488 _27489) (@lem1958962 _27488 _27489 _27486 _27487)). Qed.
Lemma lem1958999 (x : real) (y : real) : term136 x y.
Proof. exact (@lem1958998 (sqrt x) (term56 y) (sqrt x) y). Qed.
Lemma lem1959002 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term38 x y.
Proof. exact (@lem1958999 x y (@lem1958996 x y h1 h2 h3)). Qed.
Lemma lem1959003 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term137 x y.
Proof. exact (fun h0 : term68 x y => @lem1959002 x y h1 h2 h3). Qed.
Lemma lem1959005 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1959006 (x : real) (y : real) : (term137 x y) = (term38 x y).
Proof. exact (@lem1959005 (term38 x y)). Qed.
Lemma lem1959007 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term38 x y.
Proof. exact (EQ_MP (@lem1959006 x y) (@lem1959003 x y h1 h2 h3)). Qed.
Lemma lem1959010 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1959012 (x : real) (y : real) : (term68 x y) = (term138 x y).
Proof. exact (@lem1959010 (term38 x y)). Qed.
Lemma lem1959015 (x : real) (y : real) (h1 : term36 x y) : term138 x y.
Proof. exact (EQ_MP (@lem1959012 x y) (@lem1958636 x y h1)). Qed.
Lemma lem1959018 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (@lem1959015 x y h3 (@lem1959007 x y h1 h2 h3)). Qed.
Lemma lem1959019 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term139.
Proof. exact (fun h0 : ~ False => @lem1959018 x y h1 h2 h3). Qed.
Lemma lem1959021 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1959022 : term139 = False.
Proof. exact (@lem1959021 False). Qed.
Lemma lem1959023 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1959022) (@lem1959019 x y h1 h2 h3)). Qed.
Lemma lem1959024 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : (term36 x y) = False.
Proof. exact (prop_ext (fun h4 : term36 x y => @lem1959023 x y h1 h2 h3) (fun h4 : False => @lem1958518 x y h3)). Qed.
Lemma lem1959025 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1959024 x y h1 h2 h3) (@lem1958518 x y h3)). Qed.
Lemma lem1959026 (x : real) (h1 : term10) (h2 : term30) (h3 : term47 x) : False.
Proof. exact (ex_elim (@lem1958382 x h3) (fun y : real => fun h0 : term46 x y => @lem1959025 x y h1 h2 h0)). Qed.
Lemma lem1959027 (h1 : term10) (h2 : term30) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1958152 h3) (fun x : real => fun h0 : term52 x => @lem1959026 x h1 h2 h0)). Qed.
Lemma lem1959028 (h1 : term30) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1959027 h0 h1 h2). Qed.
Lemma lem1959029 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1959030 (h1 : term30) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1959029) (@lem1959028 h1 h2)). Qed.
Lemma lem1959031 (h1 : term30) (h2 : term3) : term13.
Proof. exact (fun h0 : term27 => @lem1959030 h1 h2). Qed.
Lemma lem1959032 (h1 : term3) : term16.
Proof. exact (fun h0 : term30 => @lem1959031 h0 h1). Qed.
Lemma lem1959033 : term18.
Proof. exact (fun h0 : term3 => @lem1959032 h0). Qed.
Lemma lem1959034 : term4.
Proof. exact (EQ_MP (@lem1958060) (@lem1959033)). Qed.
Lemma lem1959036 : term4.
Proof. exact (@lem1957877 (@lem1959034)). Qed.
Lemma lem1959037 (h1 : term3) : term15.
Proof. exact (@lem1959036 (@lem1957862 h1)). Qed.
Lemma lem1959038 (h1 : term3) : term12.
Proof. exact (@lem1959037 h1 (@lem1900729)). Qed.
Lemma lem1959039 (h1 : term3) : term8.
Proof. exact (@lem1959038 h1 (@lem1582434)). Qed.
Lemma lem1959040 (h1 : term3) : False.
Proof. exact (@lem1959039 h1 (@lem1951675)). Qed.
Lemma lem1959041 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1959040 h1) (fun h2 : False => @lem1957862 h1)). Qed.
Lemma lem1959042 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1959041 h1) (@lem1957862 h1)). Qed.
Lemma lem1959043 : term2.
Proof. exact (fun h0 : term3 => @lem1959042 h0). Qed.
Lemma lem1959044 : term1.
Proof. exact (EQ_MP (@lem1957861) (@lem1959043)). Qed.
