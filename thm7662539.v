Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7662539_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FSTCART_PASTECART_spec.
Require Import PASTECART_FST_SND_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem7660851 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term0 _140454 _140455 _140456 P.
Proof. exact (h1). Qed.
Lemma lem7660852 {_140454 _140455 _140456 : Type'} : term1 _140454 _140455 _140456.
Proof. exact (@lem7659572 _140456 _140455 _140454). Qed.
Lemma lem7660853 {_140454 _140455 _140456 N : Type'} : term2 _140454 _140455 _140456 N.
Proof. exact (@lem7643282 _140454 (finite_sum _140455 _140456) N). Qed.
Lemma lem7660854 {_140454 _140455 _140456 : Type'} : term3 _140454 _140455 _140456.
Proof. exact (@lem7643282 _140454 _140455 _140456). Qed.
Lemma lem7660856 {_140454 _140455 _140456 M : Type'} : term4 _140454 _140455 _140456 M.
Proof. exact (@lem7648197 _140454 M (finite_sum _140455 _140456)). Qed.
Lemma lem7660857 {_140454 _140455 M : Type'} : term5 _140454 _140455 M.
Proof. exact (@lem7648197 _140454 M _140455). Qed.
Lemma lem7660858 {_140454 _140455 _140456 : Type'} : term6 _140454 _140455 _140456.
Proof. exact (@lem7648197 _140454 _140455 _140456). Qed.
Lemma lem7660860 {_140454 _140455 _140456 N : Type'} : term7 _140454 _140455 _140456 N.
Proof. exact (@lem7648197 _140454 (finite_sum _140455 _140456) N). Qed.
Lemma lem7660863 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term8 _140454 _140455 _140456 M N P) : term8 _140454 _140455 _140456 M N P.
Proof. exact (h1). Qed.
Lemma lem7660864 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term9 _140454 _140455 _140456 M N P.
Proof. exact (fun h0 : term8 _140454 _140455 _140456 M N P => @lem7660863 _140454 _140455 _140456 M N P h0). Qed.
Lemma lem7660865 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term9 _140454 _140455 _140456 M N P) : term9 _140454 _140455 _140456 M N P.
Proof. exact (h1). Qed.
Lemma lem7660866 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term8 _140454 _140455 _140456 M N P) : term8 _140454 _140455 _140456 M N P.
Proof. exact (h1). Qed.
Lemma lem7660867 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term8 _140454 _140455 _140456 M N P) (h2 : term9 _140454 _140455 _140456 M N P) : term8 _140454 _140455 _140456 M N P.
Proof. exact (@lem7660865 _140454 _140455 _140456 M N P h2 (@lem7660866 _140454 _140455 _140456 M N P h1)). Qed.
Lemma lem7660868 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term8 _140454 _140455 _140456 M N P) : term10 _140454 _140455 _140456 M N P.
Proof. exact (fun h0 : term9 _140454 _140455 _140456 M N P => @lem7660867 _140454 _140455 _140456 M N P h1 h0). Qed.
Lemma lem7660869 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term9 _140454 _140455 _140456 M N P) : term9 _140454 _140455 _140456 M N P.
Proof. exact (h1). Qed.
Lemma lem7660870 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term8 _140454 _140455 _140456 M N P) (h2 : term9 _140454 _140455 _140456 M N P) : term8 _140454 _140455 _140456 M N P.
Proof. exact (@lem7660868 _140454 _140455 _140456 M N P h1 (@lem7660869 _140454 _140455 _140456 M N P h2)). Qed.
Lemma lem7660871 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term9 _140454 _140455 _140456 M N P) : term9 _140454 _140455 _140456 M N P.
Proof. exact (fun h0 : term8 _140454 _140455 _140456 M N P => @lem7660870 _140454 _140455 _140456 M N P h0 h1). Qed.
Lemma lem7660872 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term11 _140454 _140455 _140456 M N P.
Proof. exact (fun h0 : term9 _140454 _140455 _140456 M N P => @lem7660871 _140454 _140455 _140456 M N P h0). Qed.
Lemma lem7660875 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term9 _140454 _140455 _140456 M N P.
Proof. exact (@lem7660872 _140454 _140455 _140456 M N P (@lem7660864 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7660876 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term9 _140454 _140455 _140456 M N P.
Proof. exact (@lem7660875 _140454 _140455 _140456 M N P). Qed.
Lemma lem7660956 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7660957 {_140454 _140455 _140456 : Type'} : (term12 _140454 _140455 _140456) = (term13 _140454 _140455 _140456).
Proof. exact (@lem7660956 (term1 _140454 _140455 _140456)). Qed.
Lemma lem7660962 {_140454 _140455 _140456 N : Type'} : (term14 _140454 _140455 _140456 N) = (term14 _140454 _140455 _140456 N).
Proof. exact (eq_refl (term14 _140454 _140455 _140456 N)). Qed.
Lemma lem7660963 {_140454 _140455 _140456 N : Type'} : (term15 _140454 _140455 _140456 N) = (term16 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7660962 _140454 _140455 _140456 N) (@lem7660957 _140454 _140455 _140456)). Qed.
Lemma lem7660966 {_140454 _140455 _140456 : Type'} : (term17 _140454 _140455 _140456) = (term17 _140454 _140455 _140456).
Proof. exact (eq_refl (term17 _140454 _140455 _140456)). Qed.
Lemma lem7660967 {_140454 _140455 _140456 N : Type'} : (term18 _140454 _140455 _140456 N) = (term19 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7660966 _140454 _140455 _140456) (@lem7660963 _140454 _140455 _140456 N)). Qed.
Lemma lem7660970 {_140454 _140455 _140456 N : Type'} : (term20 _140454 _140455 _140456 N) = (term20 _140454 _140455 _140456 N).
Proof. exact (eq_refl (term20 _140454 _140455 _140456 N)). Qed.
Lemma lem7660971 {_140454 _140455 _140456 N : Type'} : (term21 _140454 _140455 _140456 N) = (term22 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7660970 _140454 _140455 _140456 N) (@lem7660967 _140454 _140455 _140456 N)). Qed.
Lemma lem7660974 {_140454 _140455 _140456 M : Type'} : (term23 _140454 _140455 _140456 M) = (term23 _140454 _140455 _140456 M).
Proof. exact (eq_refl (term23 _140454 _140455 _140456 M)). Qed.
Lemma lem7660975 {_140454 _140455 _140456 M N : Type'} : (term24 _140454 _140455 _140456 M N) = (term25 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7660974 _140454 _140455 _140456 M) (@lem7660971 _140454 _140455 _140456 N)). Qed.
Lemma lem7660978 {_140454 _140455 M : Type'} : (term26 _140454 _140455 M) = (term26 _140454 _140455 M).
Proof. exact (eq_refl (term26 _140454 _140455 M)). Qed.
Lemma lem7660979 {_140454 _140455 _140456 M N : Type'} : (term27 _140454 _140455 _140456 M N) = (term28 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7660978 _140454 _140455 M) (@lem7660975 _140454 _140455 _140456 M N)). Qed.
Lemma lem7660982 {_140454 _140455 _140456 : Type'} : (term29 _140454 _140455 _140456) = (term29 _140454 _140455 _140456).
Proof. exact (eq_refl (term29 _140454 _140455 _140456)). Qed.
Lemma lem7660983 {_140454 _140455 _140456 M N : Type'} : (term30 _140454 _140455 _140456 M N) = (term31 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7660982 _140454 _140455 _140456) (@lem7660979 _140454 _140455 _140456 M N)). Qed.
Lemma lem7660986 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term32 _140454 _140455 _140456 P) = (term32 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term32 _140454 _140455 _140456 P)). Qed.
Lemma lem7660987 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : (term8 _140454 _140455 _140456 M N P) = (term33 _140454 _140455 _140456 M N P).
Proof. exact (MK_COMB (@lem7660986 _140454 _140455 _140456 P) (@lem7660983 _140454 _140455 _140456 M N)). Qed.
Lemma lem7660990 {_140454 _140455 _140456 M N : Type'} : (term34 _140454 _140455 _140456 M N) = (term35 _140454 _140455 _140456 M N).
Proof. exact (fun_ext (fun P : type16 _140454 _140455 _140456 => @lem7660987 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7660991 {_140454 _140455 _140456 : Type'} : (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop)) = (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop)).
Proof. exact (eq_refl (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop))). Qed.
Lemma lem7661000 {_140454 _140455 _140456 M N : Type'} : (term36 _140454 _140455 _140456 M N) = (term37 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7660991 _140454 _140455 _140456) (@lem7660990 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661001 {_140454 _140455 _140456 : Type'} (z : type2 _140454 _140455 _140456) : ((term38 _140454 _140455 _140456 z) = z) = ((term38 _140454 _140455 _140456 z) = z).
Proof. exact (eq_refl ((term38 _140454 _140455 _140456 z) = z)). Qed.
Lemma lem7661002 {_140454 _140455 _140456 : Type'} : (term39 _140454 _140455 _140456) = (term39 _140454 _140455 _140456).
Proof. exact (fun_ext (fun z : type2 _140454 _140455 _140456 => @lem7661001 _140454 _140455 _140456 z)). Qed.
Lemma lem7661003 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661004 {_140454 _140455 _140456 : Type'} : (term1 _140454 _140455 _140456) = (term1 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661003 _140454 _140455 _140456) (@lem7661002 _140454 _140455 _140456)). Qed.
Lemma lem7661005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7661006 {_140454 _140455 _140456 : Type'} : (term13 _140454 _140455 _140456) = (term13 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661005) (@lem7661004 _140454 _140455 _140456)). Qed.
Lemma lem7661007 {_140454 _140455 _140456 N : Type'} (y : cart _140454 N) (x : type2 _140454 _140455 _140456) : ((term40 _140454 _140455 _140456 N x y) = x) = ((term40 _140454 _140455 _140456 N x y) = x).
Proof. exact (eq_refl ((term40 _140454 _140455 _140456 N x y) = x)). Qed.
Lemma lem7661008 {_140454 _140455 _140456 N : Type'} (x : type2 _140454 _140455 _140456) : (term41 _140454 _140455 _140456 N x) = (term41 _140454 _140455 _140456 N x).
Proof. exact (fun_ext (fun y : cart _140454 N => @lem7661007 _140454 _140455 _140456 N y x)). Qed.
Lemma lem7661009 {_140454 N : Type'} : (@all (cart _140454 N)) = (@all (cart _140454 N)).
Proof. exact (eq_refl (@all (cart _140454 N))). Qed.
Lemma lem7661010 {_140454 _140455 _140456 N : Type'} (x : type2 _140454 _140455 _140456) : (term42 _140454 _140455 _140456 N x) = (term42 _140454 _140455 _140456 N x).
Proof. exact (MK_COMB (@lem7661009 _140454 N) (@lem7661008 _140454 _140455 _140456 N x)). Qed.
Lemma lem7661011 {_140454 _140455 _140456 N : Type'} : (term43 _140454 _140455 _140456 N) = (term43 _140454 _140455 _140456 N).
Proof. exact (fun_ext (fun x : type2 _140454 _140455 _140456 => @lem7661010 _140454 _140455 _140456 N x)). Qed.
Lemma lem7661012 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661013 {_140454 _140455 _140456 N : Type'} : (term2 _140454 _140455 _140456 N) = (term2 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661012 _140454 _140455 _140456) (@lem7661011 _140454 _140455 _140456 N)). Qed.
Lemma lem7661014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661015 {_140454 _140455 _140456 N : Type'} : (term14 _140454 _140455 _140456 N) = (term14 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661014) (@lem7661013 _140454 _140455 _140456 N)). Qed.
Lemma lem7661016 {_140454 _140455 _140456 N : Type'} : (term16 _140454 _140455 _140456 N) = (term16 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661015 _140454 _140455 _140456 N) (@lem7661006 _140454 _140455 _140456)). Qed.
Lemma lem7661017 {_140454 _140455 _140456 : Type'} (y : cart _140454 _140456) (x : cart _140454 _140455) : ((term44 _140454 _140455 _140456 x y) = x) = ((term44 _140454 _140455 _140456 x y) = x).
Proof. exact (eq_refl ((term44 _140454 _140455 _140456 x y) = x)). Qed.
Lemma lem7661018 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) : (term45 _140454 _140455 _140456 x) = (term45 _140454 _140455 _140456 x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661017 _140454 _140455 _140456 y x)). Qed.
Lemma lem7661019 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661020 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) : (term46 _140454 _140455 _140456 x) = (term46 _140454 _140455 _140456 x).
Proof. exact (MK_COMB (@lem7661019 _140454 _140456) (@lem7661018 _140454 _140455 _140456 x)). Qed.
Lemma lem7661021 {_140454 _140455 _140456 : Type'} : (term47 _140454 _140455 _140456) = (term47 _140454 _140455 _140456).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661020 _140454 _140455 _140456 x)). Qed.
Lemma lem7661022 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661023 {_140454 _140455 _140456 : Type'} : (term3 _140454 _140455 _140456) = (term3 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661022 _140454 _140455) (@lem7661021 _140454 _140455 _140456)). Qed.
Lemma lem7661024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661025 {_140454 _140455 _140456 : Type'} : (term17 _140454 _140455 _140456) = (term17 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661024) (@lem7661023 _140454 _140455 _140456)). Qed.
Lemma lem7661026 {_140454 _140455 _140456 N : Type'} : (term19 _140454 _140455 _140456 N) = (term19 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661025 _140454 _140455 _140456) (@lem7661016 _140454 _140455 _140456 N)). Qed.
Lemma lem7661027 {_140454 _140455 _140456 N : Type'} (x : type2 _140454 _140455 _140456) (y : cart _140454 N) : ((term48 _140454 _140455 _140456 N x y) = y) = ((term48 _140454 _140455 _140456 N x y) = y).
Proof. exact (eq_refl ((term48 _140454 _140455 _140456 N x y) = y)). Qed.
Lemma lem7661028 {_140454 _140455 _140456 N : Type'} (x : type2 _140454 _140455 _140456) : (term49 _140454 _140455 _140456 N x) = (term49 _140454 _140455 _140456 N x).
Proof. exact (fun_ext (fun y : cart _140454 N => @lem7661027 _140454 _140455 _140456 N x y)). Qed.
Lemma lem7661029 {_140454 N : Type'} : (@all (cart _140454 N)) = (@all (cart _140454 N)).
Proof. exact (eq_refl (@all (cart _140454 N))). Qed.
Lemma lem7661030 {_140454 _140455 _140456 N : Type'} (x : type2 _140454 _140455 _140456) : (term50 _140454 _140455 _140456 N x) = (term50 _140454 _140455 _140456 N x).
Proof. exact (MK_COMB (@lem7661029 _140454 N) (@lem7661028 _140454 _140455 _140456 N x)). Qed.
Lemma lem7661031 {_140454 _140455 _140456 N : Type'} : (term51 _140454 _140455 _140456 N) = (term51 _140454 _140455 _140456 N).
Proof. exact (fun_ext (fun x : type2 _140454 _140455 _140456 => @lem7661030 _140454 _140455 _140456 N x)). Qed.
Lemma lem7661032 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661033 {_140454 _140455 _140456 N : Type'} : (term7 _140454 _140455 _140456 N) = (term7 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661032 _140454 _140455 _140456) (@lem7661031 _140454 _140455 _140456 N)). Qed.
Lemma lem7661034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661035 {_140454 _140455 _140456 N : Type'} : (term20 _140454 _140455 _140456 N) = (term20 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661034) (@lem7661033 _140454 _140455 _140456 N)). Qed.
Lemma lem7661036 {_140454 _140455 _140456 N : Type'} : (term22 _140454 _140455 _140456 N) = (term22 _140454 _140455 _140456 N).
Proof. exact (MK_COMB (@lem7661035 _140454 _140455 _140456 N) (@lem7661026 _140454 _140455 _140456 N)). Qed.
Lemma lem7661037 {_140454 _140455 _140456 M : Type'} (x : cart _140454 M) (y : type2 _140454 _140455 _140456) : ((term52 _140454 _140455 _140456 M x y) = y) = ((term52 _140454 _140455 _140456 M x y) = y).
Proof. exact (eq_refl ((term52 _140454 _140455 _140456 M x y) = y)). Qed.
Lemma lem7661038 {_140454 _140455 _140456 M : Type'} (x : cart _140454 M) : (term53 _140454 _140455 _140456 M x) = (term53 _140454 _140455 _140456 M x).
Proof. exact (fun_ext (fun y : type2 _140454 _140455 _140456 => @lem7661037 _140454 _140455 _140456 M x y)). Qed.
Lemma lem7661039 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661040 {_140454 _140455 _140456 M : Type'} (x : cart _140454 M) : (term54 _140454 _140455 _140456 M x) = (term54 _140454 _140455 _140456 M x).
Proof. exact (MK_COMB (@lem7661039 _140454 _140455 _140456) (@lem7661038 _140454 _140455 _140456 M x)). Qed.
Lemma lem7661041 {_140454 _140455 _140456 M : Type'} : (term55 _140454 _140455 _140456 M) = (term55 _140454 _140455 _140456 M).
Proof. exact (fun_ext (fun x : cart _140454 M => @lem7661040 _140454 _140455 _140456 M x)). Qed.
Lemma lem7661042 {_140454 M : Type'} : (@all (cart _140454 M)) = (@all (cart _140454 M)).
Proof. exact (eq_refl (@all (cart _140454 M))). Qed.
Lemma lem7661043 {_140454 _140455 _140456 M : Type'} : (term4 _140454 _140455 _140456 M) = (term4 _140454 _140455 _140456 M).
Proof. exact (MK_COMB (@lem7661042 _140454 M) (@lem7661041 _140454 _140455 _140456 M)). Qed.
Lemma lem7661044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661045 {_140454 _140455 _140456 M : Type'} : (term23 _140454 _140455 _140456 M) = (term23 _140454 _140455 _140456 M).
Proof. exact (MK_COMB (@lem7661044) (@lem7661043 _140454 _140455 _140456 M)). Qed.
Lemma lem7661046 {_140454 _140455 _140456 M N : Type'} : (term25 _140454 _140455 _140456 M N) = (term25 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7661045 _140454 _140455 _140456 M) (@lem7661036 _140454 _140455 _140456 N)). Qed.
Lemma lem7661047 {_140454 _140455 M : Type'} (x : cart _140454 M) (y : cart _140454 _140455) : ((term56 _140454 _140455 M x y) = y) = ((term56 _140454 _140455 M x y) = y).
Proof. exact (eq_refl ((term56 _140454 _140455 M x y) = y)). Qed.
Lemma lem7661048 {_140454 _140455 M : Type'} (x : cart _140454 M) : (term57 _140454 _140455 M x) = (term57 _140454 _140455 M x).
Proof. exact (fun_ext (fun y : cart _140454 _140455 => @lem7661047 _140454 _140455 M x y)). Qed.
Lemma lem7661049 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661050 {_140454 _140455 M : Type'} (x : cart _140454 M) : (term58 _140454 _140455 M x) = (term58 _140454 _140455 M x).
Proof. exact (MK_COMB (@lem7661049 _140454 _140455) (@lem7661048 _140454 _140455 M x)). Qed.
Lemma lem7661051 {_140454 _140455 M : Type'} : (term59 _140454 _140455 M) = (term59 _140454 _140455 M).
Proof. exact (fun_ext (fun x : cart _140454 M => @lem7661050 _140454 _140455 M x)). Qed.
Lemma lem7661052 {_140454 M : Type'} : (@all (cart _140454 M)) = (@all (cart _140454 M)).
Proof. exact (eq_refl (@all (cart _140454 M))). Qed.
Lemma lem7661053 {_140454 _140455 M : Type'} : (term5 _140454 _140455 M) = (term5 _140454 _140455 M).
Proof. exact (MK_COMB (@lem7661052 _140454 M) (@lem7661051 _140454 _140455 M)). Qed.
Lemma lem7661054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661055 {_140454 _140455 M : Type'} : (term26 _140454 _140455 M) = (term26 _140454 _140455 M).
Proof. exact (MK_COMB (@lem7661054) (@lem7661053 _140454 _140455 M)). Qed.
Lemma lem7661056 {_140454 _140455 _140456 M N : Type'} : (term28 _140454 _140455 _140456 M N) = (term28 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7661055 _140454 _140455 M) (@lem7661046 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661057 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) : ((term60 _140454 _140455 _140456 x y) = y) = ((term60 _140454 _140455 _140456 x y) = y).
Proof. exact (eq_refl ((term60 _140454 _140455 _140456 x y) = y)). Qed.
Lemma lem7661058 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) : (term61 _140454 _140455 _140456 x) = (term61 _140454 _140455 _140456 x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661057 _140454 _140455 _140456 x y)). Qed.
Lemma lem7661059 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661060 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) : (term62 _140454 _140455 _140456 x) = (term62 _140454 _140455 _140456 x).
Proof. exact (MK_COMB (@lem7661059 _140454 _140456) (@lem7661058 _140454 _140455 _140456 x)). Qed.
Lemma lem7661061 {_140454 _140455 _140456 : Type'} : (term63 _140454 _140455 _140456) = (term63 _140454 _140455 _140456).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661060 _140454 _140455 _140456 x)). Qed.
Lemma lem7661062 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661063 {_140454 _140455 _140456 : Type'} : (term6 _140454 _140455 _140456) = (term6 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661062 _140454 _140455) (@lem7661061 _140454 _140455 _140456)). Qed.
Lemma lem7661064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661065 {_140454 _140455 _140456 : Type'} : (term29 _140454 _140455 _140456) = (term29 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661064) (@lem7661063 _140454 _140455 _140456)). Qed.
Lemma lem7661066 {_140454 _140455 _140456 M N : Type'} : (term31 _140454 _140455 _140456 M N) = (term31 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7661065 _140454 _140455 _140456) (@lem7661056 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661067 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term64 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661068 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term65 _140454 _140455 _140456 P x) = (term65 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661067 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661069 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661070 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term66 _140454 _140455 _140456 P x) = (term66 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661069 _140454 _140456) (@lem7661068 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661071 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term67 _140454 _140455 _140456 P) = (term67 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661070 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661072 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661073 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661072 _140454 _140455) (@lem7661071 _140454 _140455 _140456 P)). Qed.
Lemma lem7661074 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7661075 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term69 _140454 _140455 _140456 P) = (term69 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661074 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661076 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661077 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term70 _140454 _140455 _140456 P) = (term70 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661076 _140454 _140455 _140456) (@lem7661075 _140454 _140455 _140456 P)). Qed.
Lemma lem7661078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661079 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term71 _140454 _140455 _140456 P) = (term71 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661078) (@lem7661077 _140454 _140455 _140456 P)). Qed.
Lemma lem7661080 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : ((term70 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P)) = ((term70 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P)).
Proof. exact (MK_COMB (@lem7661079 _140454 _140455 _140456 P) (@lem7661073 _140454 _140455 _140456 P)). Qed.
Lemma lem7661081 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7661082 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term0 _140454 _140455 _140456 P) = (term0 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661081) (@lem7661080 _140454 _140455 _140456 P)). Qed.
Lemma lem7661083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7661084 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term32 _140454 _140455 _140456 P) = (term32 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661083) (@lem7661082 _140454 _140455 _140456 P)). Qed.
Lemma lem7661085 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : (term33 _140454 _140455 _140456 M N P) = (term33 _140454 _140455 _140456 M N P).
Proof. exact (MK_COMB (@lem7661084 _140454 _140455 _140456 P) (@lem7661066 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661086 {_140454 _140455 _140456 M N : Type'} : (term35 _140454 _140455 _140456 M N) = (term35 _140454 _140455 _140456 M N).
Proof. exact (fun_ext (fun P : type16 _140454 _140455 _140456 => @lem7661085 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7661087 {_140454 _140455 _140456 : Type'} : (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop)) = (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop)).
Proof. exact (eq_refl (@all ((cart _140454 (finite_sum _140455 _140456)) -> Prop))). Qed.
Lemma lem7661088 {_140454 _140455 _140456 M N : Type'} : (term37 _140454 _140455 _140456 M N) = (term37 _140454 _140455 _140456 M N).
Proof. exact (MK_COMB (@lem7661087 _140454 _140455 _140456) (@lem7661086 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661207 {_140454 _140455 _140456 M N : Type'} : (term36 _140454 _140455 _140456 M N) = (term37 _140454 _140455 _140456 M N).
Proof. exact (TRANS (@lem7661000 _140454 _140455 _140456 M N) (@lem7661088 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661208 {_140454 _140455 _140456 M N : Type'} : (term37 _140454 _140455 _140456 M N) = (term36 _140454 _140455 _140456 M N).
Proof. exact (SYM (@lem7661207 _140454 _140455 _140456 M N)). Qed.
Lemma lem7661209 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term0 _140454 _140455 _140456 P.
Proof. exact (h1). Qed.
Lemma lem7661216 {_140454 _140455 _140456 : Type'} (h1 : term1 _140454 _140455 _140456) : term1 _140454 _140455 _140456.
Proof. exact (h1). Qed.
Lemma lem7661218 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7661219 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term72 _140454 _140455 _140456 P) = (term73 _140454 _140455 _140456 P).
Proof. exact (@lem18392 (type2 _140454 _140455 _140456) P). Qed.
Lemma lem7661220 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term74 _140454 _140455 _140456 P) = (term75 _140454 _140455 _140456 P).
Proof. exact (@lem7661219 _140454 _140455 _140456 (term69 _140454 _140455 _140456 P)). Qed.
Lemma lem7661221 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term76 _140454 _140455 _140456 P p) = (P p).
Proof. exact (eq_refl (term76 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7661224 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term77 _140454 _140455 _140456 P p) = (term78 _140454 _140455 _140456 P p).
Proof. exact (MK_COMB (@lem7661222) (@lem7661221 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661225 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term79 _140454 _140455 _140456 P) = (term80 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661224 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661226 {_140454 _140455 _140456 : Type'} : (@ex (cart _140454 (finite_sum _140455 _140456))) = (@ex (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@ex (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661227 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term75 _140454 _140455 _140456 P) = (term73 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661226 _140454 _140455 _140456) (@lem7661225 _140454 _140455 _140456 P)). Qed.
Lemma lem7661228 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term74 _140454 _140455 _140456 P) = (term73 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661220 _140454 _140455 _140456 P) (@lem7661227 _140454 _140455 _140456 P)). Qed.
Lemma lem7661229 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term69 _140454 _140455 _140456 P) = (term69 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661218 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661230 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661231 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term70 _140454 _140455 _140456 P) = (term70 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661230 _140454 _140455 _140456) (@lem7661229 _140454 _140455 _140456 P)). Qed.
Lemma lem7661233 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term64 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661234 {_140454 _140456 : Type'} (P : type24 _140454 _140456) : (term81 _140454 _140456 P) = (term82 _140454 _140456 P).
Proof. exact (@lem18392 (cart _140454 _140456) P). Qed.
Lemma lem7661235 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term83 _140454 _140455 _140456 P x) = (term84 _140454 _140455 _140456 P x).
Proof. exact (@lem7661234 _140454 _140456 (term65 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661236 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term85 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term85 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7661239 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term86 _140454 _140455 _140456 P x y) = (term87 _140454 _140455 _140456 P x y).
Proof. exact (MK_COMB (@lem7661237) (@lem7661236 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661240 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term88 _140454 _140455 _140456 P x) = (term89 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661239 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661241 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661242 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term84 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661241 _140454 _140456) (@lem7661240 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661243 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term83 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (TRANS (@lem7661235 _140454 _140455 _140456 P x) (@lem7661242 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661244 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term65 _140454 _140455 _140456 P x) = (term65 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661233 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661245 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661246 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term66 _140454 _140455 _140456 P x) = (term66 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661245 _140454 _140456) (@lem7661244 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661247 {_140454 _140455 : Type'} (P : type24 _140454 _140455) : (term81 _140454 _140455 P) = (term82 _140454 _140455 P).
Proof. exact (@lem18392 (cart _140454 _140455) P). Qed.
Lemma lem7661248 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term91 _140454 _140455 _140456 P) = (term92 _140454 _140455 _140456 P).
Proof. exact (@lem7661247 _140454 _140455 (term67 _140454 _140455 _140456 P)). Qed.
Lemma lem7661249 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term93 _140454 _140455 _140456 P x) = (term66 _140454 _140455 _140456 P x).
Proof. exact (eq_refl (term93 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7661251 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term94 _140454 _140455 _140456 P x) = (term83 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661250) (@lem7661249 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661252 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term94 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (TRANS (@lem7661251 _140454 _140455 _140456 P x) (@lem7661243 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661253 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term95 _140454 _140455 _140456 P) = (term96 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661252 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661254 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661255 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term92 _140454 _140455 _140456 P) = (term97 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661254 _140454 _140455) (@lem7661253 _140454 _140455 _140456 P)). Qed.
Lemma lem7661256 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term91 _140454 _140455 _140456 P) = (term97 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661248 _140454 _140455 _140456 P) (@lem7661255 _140454 _140455 _140456 P)). Qed.
Lemma lem7661257 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term67 _140454 _140455 _140456 P) = (term67 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661246 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661258 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661259 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661258 _140454 _140455) (@lem7661257 _140454 _140455 _140456 P)). Qed.
Lemma lem7661260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7661261 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term98 _140454 _140455 _140456 P) = (term99 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661260) (@lem7661228 _140454 _140455 _140456 P)). Qed.
Lemma lem7661262 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term100 _140454 _140455 _140456 P) = (term101 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661261 _140454 _140455 _140456 P) (@lem7661259 _140454 _140455 _140456 P)). Qed.
Lemma lem7661263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7661264 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661263) (@lem7661231 _140454 _140455 _140456 P)). Qed.
Lemma lem7661265 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term103 _140454 _140455 _140456 P) = (term104 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661264 _140454 _140455 _140456 P) (@lem7661256 _140454 _140455 _140456 P)). Qed.
Lemma lem7661266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661267 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term105 _140454 _140455 _140456 P) = (term106 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661266) (@lem7661265 _140454 _140455 _140456 P)). Qed.
Lemma lem7661268 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term107 _140454 _140455 _140456 P) = (term108 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661267 _140454 _140455 _140456 P) (@lem7661262 _140454 _140455 _140456 P)). Qed.
Lemma lem7661269 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term0 _140454 _140455 _140456 P) = (term107 _140454 _140455 _140456 P).
Proof. exact (@lem17646 (term70 _140454 _140455 _140456 P) (term68 _140454 _140455 _140456 P)). Qed.
Lemma lem7661270 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term0 _140454 _140455 _140456 P) = (term108 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661269 _140454 _140455 _140456 P) (@lem7661268 _140454 _140455 _140456 P)). Qed.
Lemma lem7661297 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7661298 {_140454 _140455 : Type'} (P : Prop) (Q : type24 _140454 _140455) : (term111 _140454 _140455 P Q) = (term112 _140454 _140455 P Q).
Proof. exact (@lem7661297 (cart _140454 _140455) P Q). Qed.
Lemma lem7661299 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term113 _140454 _140455 _140456 P) = (term114 _140454 _140455 _140456 P).
Proof. exact (@lem7661298 _140454 _140455 (term70 _140454 _140455 _140456 P) (term96 _140454 _140455 _140456 P)). Qed.
Lemma lem7661300 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term115 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (eq_refl (term115 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661301 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term116 _140454 _140455 _140456 P) = (term96 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661300 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661302 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661303 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term117 _140454 _140455 _140456 P) = (term97 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661302 _140454 _140455) (@lem7661301 _140454 _140455 _140456 P)). Qed.
Lemma lem7661304 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term102 _140454 _140455 _140456 P)). Qed.
Lemma lem7661305 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term113 _140454 _140455 _140456 P) = (term104 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661304 _140454 _140455 _140456 P) (@lem7661303 _140454 _140455 _140456 P)). Qed.
Lemma lem7661306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661307 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term118 _140454 _140455 _140456 P) = (term119 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661306) (@lem7661305 _140454 _140455 _140456 P)). Qed.
Lemma lem7661308 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term115 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (eq_refl (term115 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661309 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term102 _140454 _140455 _140456 P)). Qed.
Lemma lem7661310 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term120 _140454 _140455 _140456 P x) = (term121 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661309 _140454 _140455 _140456 P) (@lem7661308 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661311 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term122 _140454 _140455 _140456 P) = (term123 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661310 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661312 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661313 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term114 _140454 _140455 _140456 P) = (term124 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661312 _140454 _140455) (@lem7661311 _140454 _140455 _140456 P)). Qed.
Lemma lem7661314 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : ((term113 _140454 _140455 _140456 P) = (term114 _140454 _140455 _140456 P)) = ((term104 _140454 _140455 _140456 P) = (term124 _140454 _140455 _140456 P)).
Proof. exact (MK_COMB (@lem7661307 _140454 _140455 _140456 P) (@lem7661313 _140454 _140455 _140456 P)). Qed.
Lemma lem7661315 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term104 _140454 _140455 _140456 P) = (term124 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7661314 _140454 _140455 _140456 P) (@lem7661299 _140454 _140455 _140456 P)). Qed.
Lemma lem7661317 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7661318 {_140454 _140456 : Type'} (P : Prop) (Q : type24 _140454 _140456) : (term111 _140454 _140456 P Q) = (term112 _140454 _140456 P Q).
Proof. exact (@lem7661317 (cart _140454 _140456) P Q). Qed.
Lemma lem7661319 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term125 _140454 _140455 _140456 P x) = (term126 _140454 _140455 _140456 P x).
Proof. exact (@lem7661318 _140454 _140456 (term70 _140454 _140455 _140456 P) (term89 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661320 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term127 _140454 _140455 _140456 P x y) = (term87 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term127 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661321 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term128 _140454 _140455 _140456 P x) = (term89 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661320 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661322 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661323 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term129 _140454 _140455 _140456 P x) = (term90 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661322 _140454 _140456) (@lem7661321 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661324 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term102 _140454 _140455 _140456 P)). Qed.
Lemma lem7661325 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term125 _140454 _140455 _140456 P x) = (term121 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661324 _140454 _140455 _140456 P) (@lem7661323 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661327 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term130 _140454 _140455 _140456 P x) = (term131 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661326) (@lem7661325 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661328 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term127 _140454 _140455 _140456 P x y) = (term87 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term127 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661329 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term102 _140454 _140455 _140456 P)). Qed.
Lemma lem7661330 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term132 _140454 _140455 _140456 P x y) = (term133 _140454 _140455 _140456 P x y).
Proof. exact (MK_COMB (@lem7661329 _140454 _140455 _140456 P) (@lem7661328 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661331 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term134 _140454 _140455 _140456 P x) = (term135 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661330 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661332 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661333 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term126 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661332 _140454 _140456) (@lem7661331 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661334 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : ((term125 _140454 _140455 _140456 P x) = (term126 _140454 _140455 _140456 P x)) = ((term121 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x)).
Proof. exact (MK_COMB (@lem7661327 _140454 _140455 _140456 P x) (@lem7661333 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661335 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term121 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x).
Proof. exact (EQ_MP (@lem7661334 _140454 _140455 _140456 P x) (@lem7661319 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661336 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term123 _140454 _140455 _140456 P) = (term137 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661335 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661337 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661338 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term124 _140454 _140455 _140456 P) = (term138 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661337 _140454 _140455) (@lem7661336 _140454 _140455 _140456 P)). Qed.
Lemma lem7661339 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term104 _140454 _140455 _140456 P) = (term138 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661315 _140454 _140455 _140456 P) (@lem7661338 _140454 _140455 _140456 P)). Qed.
Lemma lem7661340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661341 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term106 _140454 _140455 _140456 P) = (term139 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661340) (@lem7661339 _140454 _140455 _140456 P)). Qed.
Lemma lem7661343 {A : Type'} (P : A -> Prop) (Q : Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7661344 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (Q : Prop) : (term142 _140454 _140455 _140456 P Q) = (term143 _140454 _140455 _140456 P Q).
Proof. exact (@lem7661343 (type2 _140454 _140455 _140456) P Q). Qed.
Lemma lem7661345 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term144 _140454 _140455 _140456 P) = (term145 _140454 _140455 _140456 P).
Proof. exact (@lem7661344 _140454 _140455 _140456 (term80 _140454 _140455 _140456 P) (term68 _140454 _140455 _140456 P)). Qed.
Lemma lem7661346 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term146 _140454 _140455 _140456 P p) = (term78 _140454 _140455 _140456 P p).
Proof. exact (eq_refl (term146 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661347 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term147 _140454 _140455 _140456 P) = (term80 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661346 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661348 {_140454 _140455 _140456 : Type'} : (@ex (cart _140454 (finite_sum _140455 _140456))) = (@ex (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@ex (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661349 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term148 _140454 _140455 _140456 P) = (term73 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661348 _140454 _140455 _140456) (@lem7661347 _140454 _140455 _140456 P)). Qed.
Lemma lem7661350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7661351 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term149 _140454 _140455 _140456 P) = (term99 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661350) (@lem7661349 _140454 _140455 _140456 P)). Qed.
Lemma lem7661352 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term68 _140454 _140455 _140456 P)). Qed.
Lemma lem7661353 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term144 _140454 _140455 _140456 P) = (term101 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661351 _140454 _140455 _140456 P) (@lem7661352 _140454 _140455 _140456 P)). Qed.
Lemma lem7661354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661355 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term150 _140454 _140455 _140456 P) = (term151 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661354) (@lem7661353 _140454 _140455 _140456 P)). Qed.
Lemma lem7661356 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term146 _140454 _140455 _140456 P p) = (term78 _140454 _140455 _140456 P p).
Proof. exact (eq_refl (term146 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7661358 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term152 _140454 _140455 _140456 P p) = (term153 _140454 _140455 _140456 P p).
Proof. exact (MK_COMB (@lem7661357) (@lem7661356 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661359 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term68 _140454 _140455 _140456 P)). Qed.
Lemma lem7661360 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term154 _140454 _140455 _140456 p P) = (term155 _140454 _140455 _140456 p P).
Proof. exact (MK_COMB (@lem7661358 _140454 _140455 _140456 P p) (@lem7661359 _140454 _140455 _140456 P)). Qed.
Lemma lem7661361 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term156 _140454 _140455 _140456 P) = (term157 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661360 _140454 _140455 _140456 p P)). Qed.
Lemma lem7661362 {_140454 _140455 _140456 : Type'} : (@ex (cart _140454 (finite_sum _140455 _140456))) = (@ex (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@ex (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661363 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term145 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661362 _140454 _140455 _140456) (@lem7661361 _140454 _140455 _140456 P)). Qed.
Lemma lem7661364 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : ((term144 _140454 _140455 _140456 P) = (term145 _140454 _140455 _140456 P)) = ((term101 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P)).
Proof. exact (MK_COMB (@lem7661355 _140454 _140455 _140456 P) (@lem7661363 _140454 _140455 _140456 P)). Qed.
Lemma lem7661365 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term101 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7661364 _140454 _140455 _140456 P) (@lem7661345 _140454 _140455 _140456 P)). Qed.
Lemma lem7661366 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term108 _140454 _140455 _140456 P) = (term159 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661341 _140454 _140455 _140456 P) (@lem7661365 _140454 _140455 _140456 P)). Qed.
Lemma lem7661370 {A : Type'} (P : A -> Prop) (Q : Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7661371 {_140454 _140455 : Type'} (P : type24 _140454 _140455) (Q : Prop) : (term162 _140454 _140455 P Q) = (term163 _140454 _140455 P Q).
Proof. exact (@lem7661370 (cart _140454 _140455) P Q). Qed.
Lemma lem7661372 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term164 _140454 _140455 _140456 P) = (term165 _140454 _140455 _140456 P).
Proof. exact (@lem7661371 _140454 _140455 (term137 _140454 _140455 _140456 P) (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661373 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term166 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x).
Proof. exact (eq_refl (term166 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661374 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term167 _140454 _140455 _140456 P) = (term137 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661373 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661375 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661376 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term168 _140454 _140455 _140456 P) = (term138 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661375 _140454 _140455) (@lem7661374 _140454 _140455 _140456 P)). Qed.
Lemma lem7661377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661378 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term169 _140454 _140455 _140456 P) = (term139 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661377) (@lem7661376 _140454 _140455 _140456 P)). Qed.
Lemma lem7661379 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term158 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661380 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term164 _140454 _140455 _140456 P) = (term159 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661378 _140454 _140455 _140456 P) (@lem7661379 _140454 _140455 _140456 P)). Qed.
Lemma lem7661381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661382 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term170 _140454 _140455 _140456 P) = (term171 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661381) (@lem7661380 _140454 _140455 _140456 P)). Qed.
Lemma lem7661383 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term166 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x).
Proof. exact (eq_refl (term166 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661385 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term172 _140454 _140455 _140456 P x) = (term173 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661384) (@lem7661383 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661386 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term158 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661387 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term174 _140454 _140455 _140456 x P) = (term175 _140454 _140455 _140456 x P).
Proof. exact (MK_COMB (@lem7661385 _140454 _140455 _140456 P x) (@lem7661386 _140454 _140455 _140456 P)). Qed.
Lemma lem7661388 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term176 _140454 _140455 _140456 P) = (term177 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661387 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661389 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661390 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term165 _140454 _140455 _140456 P) = (term178 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661389 _140454 _140455) (@lem7661388 _140454 _140455 _140456 P)). Qed.
Lemma lem7661391 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : ((term164 _140454 _140455 _140456 P) = (term165 _140454 _140455 _140456 P)) = ((term159 _140454 _140455 _140456 P) = (term178 _140454 _140455 _140456 P)).
Proof. exact (MK_COMB (@lem7661382 _140454 _140455 _140456 P) (@lem7661390 _140454 _140455 _140456 P)). Qed.
Lemma lem7661392 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term159 _140454 _140455 _140456 P) = (term178 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7661391 _140454 _140455 _140456 P) (@lem7661372 _140454 _140455 _140456 P)). Qed.
Lemma lem7661396 {A : Type'} (P : A -> Prop) (Q : Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7661397 {_140454 _140456 : Type'} (P : type24 _140454 _140456) (Q : Prop) : (term162 _140454 _140456 P Q) = (term163 _140454 _140456 P Q).
Proof. exact (@lem7661396 (cart _140454 _140456) P Q). Qed.
Lemma lem7661398 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term179 _140454 _140455 _140456 x P) = (term180 _140454 _140455 _140456 x P).
Proof. exact (@lem7661397 _140454 _140456 (term135 _140454 _140455 _140456 P x) (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661399 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term181 _140454 _140455 _140456 P x y) = (term133 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term181 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661400 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term182 _140454 _140455 _140456 P x) = (term135 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661399 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661401 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661402 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term183 _140454 _140455 _140456 P x) = (term136 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661401 _140454 _140456) (@lem7661400 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661404 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term184 _140454 _140455 _140456 P x) = (term173 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661403) (@lem7661402 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661405 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term158 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661406 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term179 _140454 _140455 _140456 x P) = (term175 _140454 _140455 _140456 x P).
Proof. exact (MK_COMB (@lem7661404 _140454 _140455 _140456 P x) (@lem7661405 _140454 _140455 _140456 P)). Qed.
Lemma lem7661407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661408 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term185 _140454 _140455 _140456 x P) = (term186 _140454 _140455 _140456 x P).
Proof. exact (MK_COMB (@lem7661407) (@lem7661406 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661409 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term181 _140454 _140455 _140456 P x y) = (term133 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term181 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661411 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term187 _140454 _140455 _140456 P x y) = (term188 _140454 _140455 _140456 P x y).
Proof. exact (MK_COMB (@lem7661410) (@lem7661409 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661412 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term158 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (eq_refl (term158 _140454 _140455 _140456 P)). Qed.
Lemma lem7661413 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term189 _140454 _140455 _140456 x y P) = (term190 _140454 _140455 _140456 x y P).
Proof. exact (MK_COMB (@lem7661411 _140454 _140455 _140456 P x y) (@lem7661412 _140454 _140455 _140456 P)). Qed.
Lemma lem7661414 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term191 _140454 _140455 _140456 x P) = (term192 _140454 _140455 _140456 x P).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661413 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661415 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661416 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term180 _140454 _140455 _140456 x P) = (term193 _140454 _140455 _140456 x P).
Proof. exact (MK_COMB (@lem7661415 _140454 _140456) (@lem7661414 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661417 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : ((term179 _140454 _140455 _140456 x P) = (term180 _140454 _140455 _140456 x P)) = ((term175 _140454 _140455 _140456 x P) = (term193 _140454 _140455 _140456 x P)).
Proof. exact (MK_COMB (@lem7661408 _140454 _140455 _140456 x P) (@lem7661416 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661418 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term175 _140454 _140455 _140456 x P) = (term193 _140454 _140455 _140456 x P).
Proof. exact (EQ_MP (@lem7661417 _140454 _140455 _140456 x P) (@lem7661398 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7661421 {_140454 _140455 _140456 : Type'} (P : Prop) (Q : type16 _140454 _140455 _140456) : (term196 _140454 _140455 _140456 P Q) = (term197 _140454 _140455 _140456 P Q).
Proof. exact (@lem7661420 (type2 _140454 _140455 _140456) P Q). Qed.
Lemma lem7661422 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term198 _140454 _140455 _140456 x y P) = (term199 _140454 _140455 _140456 x y P).
Proof. exact (@lem7661421 _140454 _140455 _140456 (term133 _140454 _140455 _140456 P x y) (term157 _140454 _140455 _140456 P)). Qed.
Lemma lem7661423 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term200 _140454 _140455 _140456 P p) = (term155 _140454 _140455 _140456 p P).
Proof. exact (eq_refl (term200 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661424 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term201 _140454 _140455 _140456 P) = (term157 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661423 _140454 _140455 _140456 p P)). Qed.
Lemma lem7661425 {_140454 _140455 _140456 : Type'} : (@ex (cart _140454 (finite_sum _140455 _140456))) = (@ex (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@ex (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661426 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term202 _140454 _140455 _140456 P) = (term158 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661425 _140454 _140455 _140456) (@lem7661424 _140454 _140455 _140456 P)). Qed.
Lemma lem7661427 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term188 _140454 _140455 _140456 P x y) = (term188 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term188 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661428 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term198 _140454 _140455 _140456 x y P) = (term190 _140454 _140455 _140456 x y P).
Proof. exact (MK_COMB (@lem7661427 _140454 _140455 _140456 P x y) (@lem7661426 _140454 _140455 _140456 P)). Qed.
Lemma lem7661429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7661430 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term203 _140454 _140455 _140456 x y P) = (term204 _140454 _140455 _140456 x y P).
Proof. exact (MK_COMB (@lem7661429) (@lem7661428 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661431 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term200 _140454 _140455 _140456 P p) = (term155 _140454 _140455 _140456 p P).
Proof. exact (eq_refl (term200 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661432 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term188 _140454 _140455 _140456 P x y) = (term188 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term188 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661433 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term205 _140454 _140455 _140456 x y P p) = (term206 _140454 _140455 _140456 x y p P).
Proof. exact (MK_COMB (@lem7661432 _140454 _140455 _140456 P x y) (@lem7661431 _140454 _140455 _140456 p P)). Qed.
Lemma lem7661434 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term207 _140454 _140455 _140456 x y P) = (term208 _140454 _140455 _140456 x y P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661433 _140454 _140455 _140456 x y p P)). Qed.
Lemma lem7661435 {_140454 _140455 _140456 : Type'} : (@ex (cart _140454 (finite_sum _140455 _140456))) = (@ex (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@ex (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661436 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term199 _140454 _140455 _140456 x y P) = (term209 _140454 _140455 _140456 x y P).
Proof. exact (MK_COMB (@lem7661435 _140454 _140455 _140456) (@lem7661434 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661437 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : ((term198 _140454 _140455 _140456 x y P) = (term199 _140454 _140455 _140456 x y P)) = ((term190 _140454 _140455 _140456 x y P) = (term209 _140454 _140455 _140456 x y P)).
Proof. exact (MK_COMB (@lem7661430 _140454 _140455 _140456 x y P) (@lem7661436 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661438 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) : (term190 _140454 _140455 _140456 x y P) = (term209 _140454 _140455 _140456 x y P).
Proof. exact (EQ_MP (@lem7661437 _140454 _140455 _140456 x y P) (@lem7661422 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661439 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term192 _140454 _140455 _140456 x P) = (term210 _140454 _140455 _140456 x P).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661438 _140454 _140455 _140456 x y P)). Qed.
Lemma lem7661440 {_140454 _140456 : Type'} : (@ex (cart _140454 _140456)) = (@ex (cart _140454 _140456)).
Proof. exact (eq_refl (@ex (cart _140454 _140456))). Qed.
Lemma lem7661441 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term193 _140454 _140455 _140456 x P) = (term211 _140454 _140455 _140456 x P).
Proof. exact (MK_COMB (@lem7661440 _140454 _140456) (@lem7661439 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661442 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) : (term175 _140454 _140455 _140456 x P) = (term211 _140454 _140455 _140456 x P).
Proof. exact (TRANS (@lem7661418 _140454 _140455 _140456 x P) (@lem7661441 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661443 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term177 _140454 _140455 _140456 P) = (term212 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661442 _140454 _140455 _140456 x P)). Qed.
Lemma lem7661444 {_140454 _140455 : Type'} : (@ex (cart _140454 _140455)) = (@ex (cart _140454 _140455)).
Proof. exact (eq_refl (@ex (cart _140454 _140455))). Qed.
Lemma lem7661445 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term178 _140454 _140455 _140456 P) = (term213 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661444 _140454 _140455) (@lem7661443 _140454 _140455 _140456 P)). Qed.
Lemma lem7661446 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term159 _140454 _140455 _140456 P) = (term213 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661392 _140454 _140455 _140456 P) (@lem7661445 _140454 _140455 _140456 P)). Qed.
Lemma lem7661448 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term108 _140454 _140455 _140456 P) = (term213 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661366 _140454 _140455 _140456 P) (@lem7661446 _140454 _140455 _140456 P)). Qed.
Lemma lem7661449 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term0 _140454 _140455 _140456 P) = (term213 _140454 _140455 _140456 P).
Proof. exact (TRANS (@lem7661270 _140454 _140455 _140456 P) (@lem7661448 _140454 _140455 _140456 P)). Qed.
Lemma lem7661450 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term213 _140454 _140455 _140456 P.
Proof. exact (EQ_MP (@lem7661449 _140454 _140455 _140456 P) (@lem7661209 _140454 _140455 _140456 P h1)). Qed.
Lemma lem7661571 {_140454 _140455 _140456 : Type'} (z : type2 _140454 _140455 _140456) : ((term38 _140454 _140455 _140456 z) = z) = ((term38 _140454 _140455 _140456 z) = z).
Proof. exact (eq_refl ((term38 _140454 _140455 _140456 z) = z)). Qed.
Lemma lem7661572 {_140454 _140455 _140456 : Type'} : (term39 _140454 _140455 _140456) = (term39 _140454 _140455 _140456).
Proof. exact (fun_ext (fun z : type2 _140454 _140455 _140456 => @lem7661571 _140454 _140455 _140456 z)). Qed.
Lemma lem7661573 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661582 {_140454 _140455 _140456 : Type'} : (term1 _140454 _140455 _140456) = (term1 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661573 _140454 _140455 _140456) (@lem7661572 _140454 _140455 _140456)). Qed.
Lemma lem7661583 {_140454 _140455 _140456 : Type'} (h1 : term1 _140454 _140455 _140456) : term1 _140454 _140455 _140456.
Proof. exact (EQ_MP (@lem7661582 _140454 _140455 _140456) (@lem7661216 _140454 _140455 _140456 h1)). Qed.
Lemma lem7661584 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) (h1 : term211 _140454 _140455 _140456 x P) : term211 _140454 _140455 _140456 x P.
Proof. exact (h1). Qed.
Lemma lem7661585 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) (h1 : term209 _140454 _140455 _140456 x y P) : term209 _140454 _140455 _140456 x y P.
Proof. exact (h1). Qed.
Lemma lem7661586 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term206 _140454 _140455 _140456 x y p P) : term206 _140454 _140455 _140456 x y p P.
Proof. exact (h1). Qed.
Lemma lem7661707 {_140454 _140455 _140456 : Type'} (z : type2 _140454 _140455 _140456) : ((term38 _140454 _140455 _140456 z) = z) = ((term38 _140454 _140455 _140456 z) = z).
Proof. exact (eq_refl ((term38 _140454 _140455 _140456 z) = z)). Qed.
Lemma lem7661708 {_140454 _140455 _140456 : Type'} : (term39 _140454 _140455 _140456) = (term39 _140454 _140455 _140456).
Proof. exact (fun_ext (fun z : type2 _140454 _140455 _140456 => @lem7661707 _140454 _140455 _140456 z)). Qed.
Lemma lem7661709 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661710 {_140454 _140455 _140456 : Type'} : (term1 _140454 _140455 _140456) = (term1 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661709 _140454 _140455 _140456) (@lem7661708 _140454 _140455 _140456)). Qed.
Lemma lem7661711 {_140454 _140455 _140456 : Type'} (h1 : term1 _140454 _140455 _140456) : term1 _140454 _140455 _140456.
Proof. exact (EQ_MP (@lem7661710 _140454 _140455 _140456) (@lem7661583 _140454 _140455 _140456 h1)). Qed.
Lemma lem7661718 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term64 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661719 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term65 _140454 _140455 _140456 P x) = (term65 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661718 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661720 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661721 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term66 _140454 _140455 _140456 P x) = (term66 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661720 _140454 _140456) (@lem7661719 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661722 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term67 _140454 _140455 _140456 P) = (term67 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661721 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661723 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661724 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661723 _140454 _140455) (@lem7661722 _140454 _140455 _140456 P)). Qed.
Lemma lem7661731 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term153 _140454 _140455 _140456 P p) = (term153 _140454 _140455 _140456 P p).
Proof. exact (eq_refl (term153 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661732 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term155 _140454 _140455 _140456 p P) = (term155 _140454 _140455 _140456 p P).
Proof. exact (MK_COMB (@lem7661731 _140454 _140455 _140456 P p) (@lem7661724 _140454 _140455 _140456 P)). Qed.
Lemma lem7661741 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term87 _140454 _140455 _140456 P x y) = (term87 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term87 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661744 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7661745 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term69 _140454 _140455 _140456 P) = (term69 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661744 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661746 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661747 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term70 _140454 _140455 _140456 P) = (term70 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661746 _140454 _140455 _140456) (@lem7661745 _140454 _140455 _140456 P)). Qed.
Lemma lem7661748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7661749 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term102 _140454 _140455 _140456 P) = (term102 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661748) (@lem7661747 _140454 _140455 _140456 P)). Qed.
Lemma lem7661750 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term133 _140454 _140455 _140456 P x y) = (term133 _140454 _140455 _140456 P x y).
Proof. exact (MK_COMB (@lem7661749 _140454 _140455 _140456 P) (@lem7661741 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7661752 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term188 _140454 _140455 _140456 P x y) = (term188 _140454 _140455 _140456 P x y).
Proof. exact (MK_COMB (@lem7661751) (@lem7661750 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661753 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) : (term206 _140454 _140455 _140456 x y p P) = (term206 _140454 _140455 _140456 x y p P).
Proof. exact (MK_COMB (@lem7661752 _140454 _140455 _140456 P x y) (@lem7661732 _140454 _140455 _140456 p P)). Qed.
Lemma lem7661754 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term206 _140454 _140455 _140456 x y p P) : term206 _140454 _140455 _140456 x y p P.
Proof. exact (EQ_MP (@lem7661753 _140454 _140455 _140456 x y p P) (@lem7661586 _140454 _140455 _140456 x y p P h1)). Qed.
Lemma lem7661755 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term133 _140454 _140455 _140456 P x y.
Proof. exact (h1). Qed.
Lemma lem7661756 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term155 _140454 _140455 _140456 p P.
Proof. exact (h1). Qed.
Lemma lem7661758 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term70 _140454 _140455 _140456 P.
Proof. exact (proj1 (@lem7661755 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7661759 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term68 _140454 _140455 _140456 P.
Proof. exact (proj2 (@lem7661756 _140454 _140455 _140456 p P h1)). Qed.
Lemma lem7661829 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7661830 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term69 _140454 _140455 _140456 P) = (term69 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun p : type2 _140454 _140455 _140456 => @lem7661829 _140454 _140455 _140456 P p)). Qed.
Lemma lem7661831 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661833 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term70 _140454 _140455 _140456 P) = (term70 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661831 _140454 _140455 _140456) (@lem7661830 _140454 _140455 _140456 P)). Qed.
Lemma lem7661834 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term70 _140454 _140455 _140456 P.
Proof. exact (EQ_MP (@lem7661833 _140454 _140455 _140456 P) (@lem7661758 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7661900 {_140454 _140455 _140456 : Type'} (z : type2 _140454 _140455 _140456) : ((term38 _140454 _140455 _140456 z) = z) = ((term38 _140454 _140455 _140456 z) = z).
Proof. exact (eq_refl ((term38 _140454 _140455 _140456 z) = z)). Qed.
Lemma lem7661901 {_140454 _140455 _140456 : Type'} : (term39 _140454 _140455 _140456) = (term39 _140454 _140455 _140456).
Proof. exact (fun_ext (fun z : type2 _140454 _140455 _140456 => @lem7661900 _140454 _140455 _140456 z)). Qed.
Lemma lem7661902 {_140454 _140455 _140456 : Type'} : (@all (cart _140454 (finite_sum _140455 _140456))) = (@all (cart _140454 (finite_sum _140455 _140456))).
Proof. exact (eq_refl (@all (cart _140454 (finite_sum _140455 _140456)))). Qed.
Lemma lem7661904 {_140454 _140455 _140456 : Type'} : (term1 _140454 _140455 _140456) = (term1 _140454 _140455 _140456).
Proof. exact (MK_COMB (@lem7661902 _140454 _140455 _140456) (@lem7661901 _140454 _140455 _140456)). Qed.
Lemma lem7661905 {_140454 _140455 _140456 : Type'} (h1 : term1 _140454 _140455 _140456) : term1 _140454 _140455 _140456.
Proof. exact (EQ_MP (@lem7661904 _140454 _140455 _140456) (@lem7661711 _140454 _140455 _140456 h1)). Qed.
Lemma lem7661911 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term64 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (eq_refl (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661912 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term65 _140454 _140455 _140456 P x) = (term65 _140454 _140455 _140456 P x).
Proof. exact (fun_ext (fun y : cart _140454 _140456 => @lem7661911 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7661913 {_140454 _140456 : Type'} : (@all (cart _140454 _140456)) = (@all (cart _140454 _140456)).
Proof. exact (eq_refl (@all (cart _140454 _140456))). Qed.
Lemma lem7661914 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) : (term66 _140454 _140455 _140456 P x) = (term66 _140454 _140455 _140456 P x).
Proof. exact (MK_COMB (@lem7661913 _140454 _140456) (@lem7661912 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661915 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term67 _140454 _140455 _140456 P) = (term67 _140454 _140455 _140456 P).
Proof. exact (fun_ext (fun x : cart _140454 _140455 => @lem7661914 _140454 _140455 _140456 P x)). Qed.
Lemma lem7661916 {_140454 _140455 : Type'} : (@all (cart _140454 _140455)) = (@all (cart _140454 _140455)).
Proof. exact (eq_refl (@all (cart _140454 _140455))). Qed.
Lemma lem7661918 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term68 _140454 _140455 _140456 P) = (term68 _140454 _140455 _140456 P).
Proof. exact (MK_COMB (@lem7661916 _140454 _140455) (@lem7661915 _140454 _140455 _140456 P)). Qed.
Lemma lem7661919 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term68 _140454 _140455 _140456 P.
Proof. exact (EQ_MP (@lem7661918 _140454 _140455 _140456 P) (@lem7661759 _140454 _140455 _140456 p P h1)). Qed.
Lemma lem7661959 {_140454 _140455 _140456 : Type'} (_98604 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term76 _140454 _140455 _140456 P _98604.
Proof. exact (@lem7661834 _140454 _140455 _140456 P x y h1 _98604). Qed.
Lemma lem7661960 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98604 : type2 _140454 _140455 _140456) : (term76 _140454 _140455 _140456 P _98604) = (P _98604).
Proof. exact (eq_refl (term76 _140454 _140455 _140456 P _98604)). Qed.
Lemma lem7661998 {_140454 _140455 _140456 : Type'} (_98617 : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : term214 _140454 _140455 _140456 _98617.
Proof. exact (@lem7661905 _140454 _140455 _140456 h1 _98617). Qed.
Lemma lem7661999 {_140454 _140455 _140456 : Type'} (_98617 : type2 _140454 _140455 _140456) : (term214 _140454 _140455 _140456 _98617) = ((term38 _140454 _140455 _140456 _98617) = _98617).
Proof. exact (eq_refl (term214 _140454 _140455 _140456 _98617)). Qed.
Lemma lem7662001 {_140454 _140455 _140456 : Type'} (_98618 : cart _140454 _140455) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term93 _140454 _140455 _140456 P _98618.
Proof. exact (@lem7661919 _140454 _140455 _140456 p P h1 _98618). Qed.
Lemma lem7662002 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98618 : cart _140454 _140455) : (term93 _140454 _140455 _140456 P _98618) = (term66 _140454 _140455 _140456 P _98618).
Proof. exact (eq_refl (term93 _140454 _140455 _140456 P _98618)). Qed.
Lemma lem7662003 {_140454 _140455 _140456 : Type'} (_98618 : cart _140454 _140455) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term66 _140454 _140455 _140456 P _98618.
Proof. exact (EQ_MP (@lem7662002 _140454 _140455 _140456 P _98618) (@lem7662001 _140454 _140455 _140456 _98618 p P h1)). Qed.
Lemma lem7662004 {_140454 _140455 _140456 : Type'} (_98618 : cart _140454 _140455) (_98619 : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term85 _140454 _140455 _140456 P _98618 _98619.
Proof. exact (@lem7662003 _140454 _140455 _140456 _98618 p P h1 _98619). Qed.
Lemma lem7662005 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98618 : cart _140454 _140455) (_98619 : cart _140454 _140456) : (term85 _140454 _140455 _140456 P _98618 _98619) = (term64 _140454 _140455 _140456 P _98618 _98619).
Proof. exact (eq_refl (term85 _140454 _140455 _140456 P _98618 _98619)). Qed.
Lemma lem7662024 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term87 _140454 _140455 _140456 P x y.
Proof. exact (proj2 (@lem7661755 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7662040 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term78 _140454 _140455 _140456 P p.
Proof. exact (proj1 (@lem7661756 _140454 _140455 _140456 p P h1)). Qed.
Lemma lem7662180 {_140454 _140455 _140456 : Type'} (_98604 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : P _98604.
Proof. exact (EQ_MP (@lem7661960 _140454 _140455 _140456 P _98604) (@lem7661959 _140454 _140455 _140456 _98604 P x y h1)). Qed.
Lemma lem7662181 {_140454 _140455 _140456 : Type'} (_98604 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : P _98604.
Proof. exact (@lem7662180 _140454 _140455 _140456 _98604 P x y h1). Qed.
Lemma lem7662182 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term64 _140454 _140455 _140456 P x y.
Proof. exact (@lem7662181 _140454 _140455 _140456 (@pastecart _140454 _140455 _140456 x y) P x y h1). Qed.
Lemma lem7662183 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term215 _140454 _140455 _140456 P x y.
Proof. exact (fun h0 : term87 _140454 _140455 _140456 P x y => @lem7662182 _140454 _140455 _140456 P x y h1). Qed.
Lemma lem7662185 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662186 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term215 _140454 _140455 _140456 P x y) = (term64 _140454 _140455 _140456 P x y).
Proof. exact (@lem7662185 (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7662187 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term64 _140454 _140455 _140456 P x y.
Proof. exact (EQ_MP (@lem7662186 _140454 _140455 _140456 P x y) (@lem7662183 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7662190 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7662192 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) : (term87 _140454 _140455 _140456 P x y) = (term217 _140454 _140455 _140456 P x y).
Proof. exact (@lem7662190 (term64 _140454 _140455 _140456 P x y)). Qed.
Lemma lem7662195 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term217 _140454 _140455 _140456 P x y.
Proof. exact (EQ_MP (@lem7662192 _140454 _140455 _140456 P x y) (@lem7662024 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7662198 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : False.
Proof. exact (@lem7662195 _140454 _140455 _140456 P x y h1 (@lem7662187 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7662199 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : term218.
Proof. exact (fun h0 : ~ False => @lem7662198 _140454 _140455 _140456 P x y h1). Qed.
Lemma lem7662201 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662202 : term218 = False.
Proof. exact (@lem7662201 False). Qed.
Lemma lem7662203 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (x : cart _140454 _140455) (y : cart _140454 _140456) (h1 : term133 _140454 _140455 _140456 P x y) : False.
Proof. exact (EQ_MP (@lem7662202) (@lem7662199 _140454 _140455 _140456 P x y h1)). Qed.
Lemma lem7662204 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7662205 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) (h1 : _98650 = _98651) : _98650 = _98651.
Proof. exact (h1). Qed.
Lemma lem7662206 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) (h1 : _98650 = _98651) : (P _98650) = (P _98651).
Proof. exact (MK_COMB (@lem7662204 _140454 _140455 _140456 P) (@lem7662205 _140454 _140455 _140456 _98650 _98651 h1)). Qed.
Lemma lem7662208 (b : Prop) (a : Prop) : term219 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7662209 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : term220 _140454 _140455 _140456 _98651 P _98650.
Proof. exact (@lem7662208 (P _98651) (P _98650)). Qed.
Lemma lem7662210 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) (h1 : _98650 = _98651) : term221 _140454 _140455 _140456 _98651 P _98650.
Proof. exact (@lem7662209 _140454 _140455 _140456 _98651 P _98650 (@lem7662206 _140454 _140455 _140456 P _98650 _98651 h1)). Qed.
Lemma lem7662211 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : term222 _140454 _140455 _140456 _98651 P _98650.
Proof. exact (fun h0 : _98650 = _98651 => @lem7662210 _140454 _140455 _140456 P _98650 _98651 h0). Qed.
Lemma lem7662213 (a : Prop) (b : Prop) : (a -> b) = (term223 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7662214 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term222 _140454 _140455 _140456 _98651 P _98650) = (term224 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (@lem7662213 (_98650 = _98651) (term221 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662215 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : term224 _140454 _140455 _140456 _98651 P _98650.
Proof. exact (EQ_MP (@lem7662214 _140454 _140455 _140456 _98651 P _98650) (@lem7662211 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662341 {_140454 _140455 _140456 : Type'} (_98617 : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : (term38 _140454 _140455 _140456 _98617) = _98617.
Proof. exact (EQ_MP (@lem7661999 _140454 _140455 _140456 _98617) (@lem7661998 _140454 _140455 _140456 _98617 h1)). Qed.
Lemma lem7662342 {_140454 _140455 _140456 : Type'} (_98617 : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : (term38 _140454 _140455 _140456 _98617) = _98617.
Proof. exact (@lem7662341 _140454 _140455 _140456 _98617 h1). Qed.
Lemma lem7662343 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : (term38 _140454 _140455 _140456 p) = p.
Proof. exact (@lem7662342 _140454 _140455 _140456 p h1). Qed.
Lemma lem7662344 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : term225 _140454 _140455 _140456 p.
Proof. exact (fun h0 : term226 _140454 _140455 _140456 p => @lem7662343 _140454 _140455 _140456 p h1). Qed.
Lemma lem7662346 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662347 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) : (term225 _140454 _140455 _140456 p) = ((term38 _140454 _140455 _140456 p) = p).
Proof. exact (@lem7662346 ((term38 _140454 _140455 _140456 p) = p)). Qed.
Lemma lem7662348 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) : (term38 _140454 _140455 _140456 p) = p.
Proof. exact (EQ_MP (@lem7662347 _140454 _140455 _140456 p) (@lem7662344 _140454 _140455 _140456 p h1)). Qed.
Lemma lem7662350 {_140454 _140455 _140456 : Type'} (_98618 : cart _140454 _140455) (_98619 : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term64 _140454 _140455 _140456 P _98618 _98619.
Proof. exact (EQ_MP (@lem7662005 _140454 _140455 _140456 P _98618 _98619) (@lem7662004 _140454 _140455 _140456 _98618 _98619 p P h1)). Qed.
Lemma lem7662351 {_140454 _140455 _140456 : Type'} (_98618 : cart _140454 _140455) (_98619 : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term64 _140454 _140455 _140456 P _98618 _98619.
Proof. exact (@lem7662350 _140454 _140455 _140456 _98618 _98619 p P h1). Qed.
Lemma lem7662352 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term227 _140454 _140455 _140456 P p.
Proof. exact (@lem7662351 _140454 _140455 _140456 (@fstcart _140454 _140455 _140456 p) (@sndcart _140454 _140455 _140456 p) p P h1). Qed.
Lemma lem7662353 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term228 _140454 _140455 _140456 P p.
Proof. exact (fun h0 : term229 _140454 _140455 _140456 P p => @lem7662352 _140454 _140455 _140456 p P h1). Qed.
Lemma lem7662355 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662356 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term228 _140454 _140455 _140456 P p) = (term227 _140454 _140455 _140456 P p).
Proof. exact (@lem7662355 (term227 _140454 _140455 _140456 P p)). Qed.
Lemma lem7662357 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term227 _140454 _140455 _140456 P p.
Proof. exact (EQ_MP (@lem7662356 _140454 _140455 _140456 P p) (@lem7662353 _140454 _140455 _140456 p P h1)). Qed.
Lemma lem7662363 (q : Prop) (p : Prop) (r : Prop) : (term230 p q r) = (term230 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7662364 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term224 _140454 _140455 _140456 _98651 P _98650) = (term231 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (@lem7662363 (P _98651) (term232 _140454 _140455 _140456 _98650 _98651) (term78 _140454 _140455 _140456 P _98650)). Qed.
Lemma lem7662378 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7662379 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term233 _140454 _140455 _140456 _98651 P _98650) = (term234 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (@lem7662378 (term78 _140454 _140455 _140456 P _98650) (term232 _140454 _140455 _140456 _98650 _98651)). Qed.
Lemma lem7662387 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term235 _140454 _140455 _140456 P _98651) = (term235 _140454 _140455 _140456 P _98651).
Proof. exact (eq_refl (term235 _140454 _140455 _140456 P _98651)). Qed.
Lemma lem7662388 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term231 _140454 _140455 _140456 _98651 P _98650) = (term236 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (MK_COMB (@lem7662387 _140454 _140455 _140456 P _98651) (@lem7662379 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662399 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term224 _140454 _140455 _140456 _98651 P _98650) = (term236 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (TRANS (@lem7662364 _140454 _140455 _140456 _98651 P _98650) (@lem7662388 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7662401 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term237 _140454 _140455 _140456 _98651 P _98650) = (term238 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (MK_COMB (@lem7662400) (@lem7662399 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662415 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7662416 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term233 _140454 _140455 _140456 _98651 P _98650) = (term234 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (@lem7662415 (term78 _140454 _140455 _140456 P _98650) (term232 _140454 _140455 _140456 _98650 _98651)). Qed.
Lemma lem7662424 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term235 _140454 _140455 _140456 P _98651) = (term235 _140454 _140455 _140456 P _98651).
Proof. exact (eq_refl (term235 _140454 _140455 _140456 P _98651)). Qed.
Lemma lem7662425 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term231 _140454 _140455 _140456 _98651 P _98650) = (term236 _140454 _140455 _140456 P _98650 _98651).
Proof. exact (MK_COMB (@lem7662424 _140454 _140455 _140456 P _98651) (@lem7662416 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662436 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : ((term224 _140454 _140455 _140456 _98651 P _98650) = (term231 _140454 _140455 _140456 _98651 P _98650)) = ((term236 _140454 _140455 _140456 P _98650 _98651) = (term236 _140454 _140455 _140456 P _98650 _98651)).
Proof. exact (MK_COMB (@lem7662401 _140454 _140455 _140456 P _98650 _98651) (@lem7662425 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662438 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7662439 (x : Prop) : (x = x) = True.
Proof. exact (@lem7662438 Prop x). Qed.
Lemma lem7662440 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : ((term236 _140454 _140455 _140456 P _98650 _98651) = (term236 _140454 _140455 _140456 P _98650 _98651)) = True.
Proof. exact (@lem7662439 (term236 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662441 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : ((term224 _140454 _140455 _140456 _98651 P _98650) = (term231 _140454 _140455 _140456 _98651 P _98650)) = True.
Proof. exact (TRANS (@lem7662436 _140454 _140455 _140456 P _98650 _98651) (@lem7662440 _140454 _140455 _140456 P _98650 _98651)). Qed.
Lemma lem7662442 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : True = ((term224 _140454 _140455 _140456 _98651 P _98650) = (term231 _140454 _140455 _140456 _98651 P _98650)).
Proof. exact (SYM (@lem7662441 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662443 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term224 _140454 _140455 _140456 _98651 P _98650) = (term231 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (EQ_MP (@lem7662442 _140454 _140455 _140456 _98651 P _98650) (@lem0)). Qed.
Lemma lem7662444 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : term231 _140454 _140455 _140456 _98651 P _98650.
Proof. exact (EQ_MP (@lem7662443 _140454 _140455 _140456 _98651 P _98650) (@lem7662215 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662446 (b : Prop) (a : Prop) : (a \/ b) = (term239 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7662447 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term231 _140454 _140455 _140456 _98651 P _98650) = (term240 _140454 _140455 _140456 _98650 P _98651).
Proof. exact (@lem7662446 (term233 _140454 _140455 _140456 _98651 P _98650) (P _98651)). Qed.
Lemma lem7662449 (a : Prop) (b : Prop) : (term241 a b) = (term242 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7662450 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term243 _140454 _140455 _140456 _98651 P _98650) = (term244 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (@lem7662449 (term232 _140454 _140455 _140456 _98650 _98651) (term78 _140454 _140455 _140456 P _98650)). Qed.
Lemma lem7662452 (a : Prop) : (term245 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7662453 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term246 _140454 _140455 _140456 _98650 _98651) = (_98650 = _98651).
Proof. exact (@lem7662452 (_98650 = _98651)). Qed.
Lemma lem7662454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7662455 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term247 _140454 _140455 _140456 _98650 _98651) = (term248 _140454 _140455 _140456 _98650 _98651).
Proof. exact (MK_COMB (@lem7662454) (@lem7662453 _140454 _140455 _140456 _98650 _98651)). Qed.
Lemma lem7662457 (a : Prop) : (term245 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7662458 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term249 _140454 _140455 _140456 P _98650) = (P _98650).
Proof. exact (@lem7662457 (P _98650)). Qed.
Lemma lem7662459 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term244 _140454 _140455 _140456 _98651 P _98650) = (term250 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (MK_COMB (@lem7662455 _140454 _140455 _140456 _98650 _98651) (@lem7662458 _140454 _140455 _140456 P _98650)). Qed.
Lemma lem7662460 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term243 _140454 _140455 _140456 _98651 P _98650) = (term250 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (TRANS (@lem7662450 _140454 _140455 _140456 _98651 P _98650) (@lem7662459 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662462 {_140454 _140455 _140456 : Type'} (_98651 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98650 : type2 _140454 _140455 _140456) : (term251 _140454 _140455 _140456 _98651 P _98650) = (term252 _140454 _140455 _140456 _98651 P _98650).
Proof. exact (MK_COMB (@lem7662461) (@lem7662460 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662463 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (P _98651) = (P _98651).
Proof. exact (eq_refl (P _98651)). Qed.
Lemma lem7662464 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term240 _140454 _140455 _140456 _98650 P _98651) = (term253 _140454 _140455 _140456 _98650 P _98651).
Proof. exact (MK_COMB (@lem7662462 _140454 _140455 _140456 _98651 P _98650) (@lem7662463 _140454 _140455 _140456 P _98651)). Qed.
Lemma lem7662465 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : (term231 _140454 _140455 _140456 _98651 P _98650) = (term253 _140454 _140455 _140456 _98650 P _98651).
Proof. exact (TRANS (@lem7662447 _140454 _140455 _140456 _98650 P _98651) (@lem7662464 _140454 _140455 _140456 _98650 P _98651)). Qed.
Lemma lem7662467 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : term254 _140454 _140455 _140456 P p.
Proof. exact (conj (@lem7662348 _140454 _140455 _140456 p h1) (@lem7662357 _140454 _140455 _140456 p P h2)). Qed.
Lemma lem7662469 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : term253 _140454 _140455 _140456 _98650 P _98651.
Proof. exact (EQ_MP (@lem7662465 _140454 _140455 _140456 _98650 P _98651) (@lem7662444 _140454 _140455 _140456 _98651 P _98650)). Qed.
Lemma lem7662470 {_140454 _140455 _140456 : Type'} (_98650 : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (_98651 : type2 _140454 _140455 _140456) : term253 _140454 _140455 _140456 _98650 P _98651.
Proof. exact (@lem7662469 _140454 _140455 _140456 _98650 P _98651). Qed.
Lemma lem7662471 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : term255 _140454 _140455 _140456 P p.
Proof. exact (@lem7662470 _140454 _140455 _140456 (term38 _140454 _140455 _140456 p) P p). Qed.
Lemma lem7662474 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : P p.
Proof. exact (@lem7662471 _140454 _140455 _140456 P p (@lem7662467 _140454 _140455 _140456 p P h1 h2)). Qed.
Lemma lem7662475 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : term256 _140454 _140455 _140456 P p.
Proof. exact (fun h0 : term78 _140454 _140455 _140456 P p => @lem7662474 _140454 _140455 _140456 p P h1 h2). Qed.
Lemma lem7662477 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662478 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term256 _140454 _140455 _140456 P p) = (P p).
Proof. exact (@lem7662477 (P p)). Qed.
Lemma lem7662479 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : P p.
Proof. exact (EQ_MP (@lem7662478 _140454 _140455 _140456 P p) (@lem7662475 _140454 _140455 _140456 p P h1 h2)). Qed.
Lemma lem7662482 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7662484 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (p : type2 _140454 _140455 _140456) : (term78 _140454 _140455 _140456 P p) = (term257 _140454 _140455 _140456 P p).
Proof. exact (@lem7662482 (P p)). Qed.
Lemma lem7662487 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term155 _140454 _140455 _140456 p P) : term257 _140454 _140455 _140456 P p.
Proof. exact (EQ_MP (@lem7662484 _140454 _140455 _140456 P p) (@lem7662040 _140454 _140455 _140456 p P h1)). Qed.
Lemma lem7662490 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : False.
Proof. exact (@lem7662487 _140454 _140455 _140456 p P h2 (@lem7662479 _140454 _140455 _140456 p P h1 h2)). Qed.
Lemma lem7662491 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : term218.
Proof. exact (fun h0 : ~ False => @lem7662490 _140454 _140455 _140456 p P h1 h2). Qed.
Lemma lem7662493 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7662494 : term218 = False.
Proof. exact (@lem7662493 False). Qed.
Lemma lem7662495 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : False.
Proof. exact (EQ_MP (@lem7662494) (@lem7662491 _140454 _140455 _140456 p P h1 h2)). Qed.
Lemma lem7662496 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : (term1 _140454 _140455 _140456) = False.
Proof. exact (prop_ext (fun h3 : term1 _140454 _140455 _140456 => @lem7662495 _140454 _140455 _140456 p P h1 h2) (fun h3 : False => @lem7661905 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662497 {_140454 _140455 _140456 : Type'} (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term155 _140454 _140455 _140456 p P) : False.
Proof. exact (EQ_MP (@lem7662496 _140454 _140455 _140456 p P h1 h2) (@lem7661905 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662498 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term206 _140454 _140455 _140456 x y p P) : False.
Proof. exact (or_elim (@lem7661754 _140454 _140455 _140456 x y p P h2) (fun h0 : term133 _140454 _140455 _140456 P x y => @lem7662203 _140454 _140455 _140456 P x y h0) (fun h0 : term155 _140454 _140455 _140456 p P => @lem7662497 _140454 _140455 _140456 p P h1 h0)). Qed.
Lemma lem7662499 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term206 _140454 _140455 _140456 x y p P) : (term206 _140454 _140455 _140456 x y p P) = False.
Proof. exact (prop_ext (fun h3 : term206 _140454 _140455 _140456 x y p P => @lem7662498 _140454 _140455 _140456 x y p P h1 h2) (fun h3 : False => @lem7661754 _140454 _140455 _140456 x y p P h2)). Qed.
Lemma lem7662500 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term206 _140454 _140455 _140456 x y p P) : False.
Proof. exact (EQ_MP (@lem7662499 _140454 _140455 _140456 x y p P h1 h2) (@lem7661754 _140454 _140455 _140456 x y p P h2)). Qed.
Lemma lem7662501 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term206 _140454 _140455 _140456 x y p P) : (term1 _140454 _140455 _140456) = False.
Proof. exact (prop_ext (fun h3 : term1 _140454 _140455 _140456 => @lem7662500 _140454 _140455 _140456 x y p P h1 h2) (fun h3 : False => @lem7661711 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662502 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (p : type2 _140454 _140455 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term206 _140454 _140455 _140456 x y p P) : False.
Proof. exact (EQ_MP (@lem7662501 _140454 _140455 _140456 x y p P h1 h2) (@lem7661711 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662503 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (y : cart _140454 _140456) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term209 _140454 _140455 _140456 x y P) : False.
Proof. exact (ex_elim (@lem7661585 _140454 _140455 _140456 x y P h2) (fun p : type2 _140454 _140455 _140456 => fun h0 : term208 _140454 _140455 _140456 x y P p => @lem7662502 _140454 _140455 _140456 x y p P h1 h0)). Qed.
Lemma lem7662504 {_140454 _140455 _140456 : Type'} (x : cart _140454 _140455) (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term211 _140454 _140455 _140456 x P) : False.
Proof. exact (ex_elim (@lem7661584 _140454 _140455 _140456 x P h2) (fun y : cart _140454 _140456 => fun h0 : term210 _140454 _140455 _140456 x P y => @lem7662503 _140454 _140455 _140456 x y P h1 h0)). Qed.
Lemma lem7662505 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term0 _140454 _140455 _140456 P) : False.
Proof. exact (ex_elim (@lem7661450 _140454 _140455 _140456 P h2) (fun x : cart _140454 _140455 => fun h0 : term212 _140454 _140455 _140456 P x => @lem7662504 _140454 _140455 _140456 x P h1 h0)). Qed.
Lemma lem7662506 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term0 _140454 _140455 _140456 P) : (term1 _140454 _140455 _140456) = False.
Proof. exact (prop_ext (fun h3 : term1 _140454 _140455 _140456 => @lem7662505 _140454 _140455 _140456 P h1 h2) (fun h3 : False => @lem7661583 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662507 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term1 _140454 _140455 _140456) (h2 : term0 _140454 _140455 _140456 P) : False.
Proof. exact (EQ_MP (@lem7662506 _140454 _140455 _140456 P h1 h2) (@lem7661583 _140454 _140455 _140456 h1)). Qed.
Lemma lem7662508 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term12 _140454 _140455 _140456.
Proof. exact (fun h0 : term1 _140454 _140455 _140456 => @lem7662507 _140454 _140455 _140456 P h0 h1). Qed.
Lemma lem7662509 {_140454 _140455 _140456 : Type'} : (term12 _140454 _140455 _140456) = (term13 _140454 _140455 _140456).
Proof. exact (@lem69 (term1 _140454 _140455 _140456)). Qed.
Lemma lem7662510 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term13 _140454 _140455 _140456.
Proof. exact (EQ_MP (@lem7662509 _140454 _140455 _140456) (@lem7662508 _140454 _140455 _140456 P h1)). Qed.
Lemma lem7662511 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term16 _140454 _140455 _140456 N.
Proof. exact (fun h0 : term2 _140454 _140455 _140456 N => @lem7662510 _140454 _140455 _140456 P h1). Qed.
Lemma lem7662512 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term19 _140454 _140455 _140456 N.
Proof. exact (fun h0 : term3 _140454 _140455 _140456 => @lem7662511 _140454 _140455 _140456 N P h1). Qed.
Lemma lem7662513 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term22 _140454 _140455 _140456 N.
Proof. exact (fun h0 : term7 _140454 _140455 _140456 N => @lem7662512 _140454 _140455 _140456 N P h1). Qed.
Lemma lem7662514 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term25 _140454 _140455 _140456 M N.
Proof. exact (fun h0 : term4 _140454 _140455 _140456 M => @lem7662513 _140454 _140455 _140456 N P h1). Qed.
Lemma lem7662515 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term28 _140454 _140455 _140456 M N.
Proof. exact (fun h0 : term5 _140454 _140455 M => @lem7662514 _140454 _140455 _140456 M N P h1). Qed.
Lemma lem7662516 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term31 _140454 _140455 _140456 M N.
Proof. exact (fun h0 : term6 _140454 _140455 _140456 => @lem7662515 _140454 _140455 _140456 M N P h1). Qed.
Lemma lem7662517 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term33 _140454 _140455 _140456 M N P.
Proof. exact (fun h0 : term0 _140454 _140455 _140456 P => @lem7662516 _140454 _140455 _140456 M N P h0). Qed.
Lemma lem7662522 {_140454 _140455 _140456 M N : Type'} : term37 _140454 _140455 _140456 M N.
Proof. exact (fun P : type16 _140454 _140455 _140456 => @lem7662517 _140454 _140455 _140456 M N P). Qed.
Lemma lem7662523 {_140454 _140455 _140456 M N : Type'} : term36 _140454 _140455 _140456 M N.
Proof. exact (EQ_MP (@lem7661208 _140454 _140455 _140456 M N) (@lem7662522 _140454 _140455 _140456 M N)). Qed.
Lemma lem7662524 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term258 _140454 _140455 _140456 M N P.
Proof. exact (@lem7662523 _140454 _140455 _140456 M N P). Qed.
Lemma lem7662525 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : (term258 _140454 _140455 _140456 M N P) = (term8 _140454 _140455 _140456 M N P).
Proof. exact (eq_refl (term258 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7662526 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term8 _140454 _140455 _140456 M N P.
Proof. exact (EQ_MP (@lem7662525 _140454 _140455 _140456 M N P) (@lem7662524 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7662528 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) : term8 _140454 _140455 _140456 M N P.
Proof. exact (@lem7660876 _140454 _140455 _140456 M N P (@lem7662526 _140454 _140455 _140456 M N P)). Qed.
Lemma lem7662529 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term30 _140454 _140455 _140456 M N.
Proof. exact (@lem7662528 _140454 _140455 _140456 M N P (@lem7660851 _140454 _140455 _140456 P h1)). Qed.
Lemma lem7662530 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term27 _140454 _140455 _140456 M N.
Proof. exact (@lem7662529 _140454 _140455 _140456 M N P h1 (@lem7660858 _140454 _140455 _140456)). Qed.
Lemma lem7662531 {_140454 _140455 _140456 M N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term24 _140454 _140455 _140456 M N.
Proof. exact (@lem7662530 _140454 _140455 _140456 M N P h1 (@lem7660857 _140454 _140455 M)). Qed.
Lemma lem7662532 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term21 _140454 _140455 _140456 N.
Proof. exact (@lem7662531 _140454 _140455 _140456 Prop N P h1 (@lem7660856 _140454 _140455 _140456 Prop)). Qed.
Lemma lem7662533 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term18 _140454 _140455 _140456 N.
Proof. exact (@lem7662532 _140454 _140455 _140456 N P h1 (@lem7660860 _140454 _140455 _140456 N)). Qed.
Lemma lem7662534 {_140454 _140455 _140456 N : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term15 _140454 _140455 _140456 N.
Proof. exact (@lem7662533 _140454 _140455 _140456 N P h1 (@lem7660854 _140454 _140455 _140456)). Qed.
Lemma lem7662535 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : term12 _140454 _140455 _140456.
Proof. exact (@lem7662534 _140454 _140455 _140456 Prop P h1 (@lem7660853 _140454 _140455 _140456 Prop)). Qed.
Lemma lem7662536 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : False.
Proof. exact (@lem7662535 _140454 _140455 _140456 P h1 (@lem7660852 _140454 _140455 _140456)). Qed.
Lemma lem7662537 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : (term0 _140454 _140455 _140456 P) = False.
Proof. exact (prop_ext (fun h2 : term0 _140454 _140455 _140456 P => @lem7662536 _140454 _140455 _140456 P h1) (fun h2 : False => @lem7660851 _140454 _140455 _140456 P h1)). Qed.
Lemma lem7662538 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) (h1 : term0 _140454 _140455 _140456 P) : False.
Proof. exact (EQ_MP (@lem7662537 _140454 _140455 _140456 P h1) (@lem7660851 _140454 _140455 _140456 P h1)). Qed.
Lemma lem7662539 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : term259 _140454 _140455 _140456 P.
Proof. exact (fun h0 : term0 _140454 _140455 _140456 P => @lem7662538 _140454 _140455 _140456 P h0). Qed.
