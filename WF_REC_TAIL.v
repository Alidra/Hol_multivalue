Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_TAIL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_AND_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LT_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SELECT_UNIQUE_spec.
Require Import SKOLEM_THM_spec.
Require Import num_CASES_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm75635_spec.
Require Import thm82_spec.
Lemma lem388789 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem388790 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (@lem388789 (term1 P)). Qed.
Lemma lem388791 (P : nat -> Prop) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem388790 P)). Qed.
Lemma lem388792 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem388795 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem388796 (P : nat -> Prop) : term5 P.
Proof. exact (fun h0 : term4 P => @lem388795 P h0). Qed.
Lemma lem388797 (P : nat -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem388798 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem388799 (P : nat -> Prop) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem388797 P h2 (@lem388798 P h1)). Qed.
Lemma lem388800 (P : nat -> Prop) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem388799 P h1 h0). Qed.
Lemma lem388801 (P : nat -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem388802 (P : nat -> Prop) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem388800 P h1 (@lem388801 P h2)). Qed.
Lemma lem388803 (P : nat -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem388802 P h0 h1). Qed.
Lemma lem388804 (P : nat -> Prop) : term7 P.
Proof. exact (fun h0 : term5 P => @lem388803 P h0). Qed.
Lemma lem388807 (P : nat -> Prop) : term5 P.
Proof. exact (@lem388804 P (@lem388796 P)). Qed.
Lemma lem388831 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem388832 : term8 = term9.
Proof. exact (@lem388831 term10). Qed.
Lemma lem388887 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem388888 : term12 = term13.
Proof. exact (MK_COMB (@lem388887) (@lem388832)). Qed.
Lemma lem388891 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (eq_refl (term14 P)). Qed.
Lemma lem388892 (P : nat -> Prop) : (term4 P) = (term15 P).
Proof. exact (MK_COMB (@lem388891 P) (@lem388888)). Qed.
Lemma lem388895 : term16 = term17.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem388892 P)). Qed.
Lemma lem388896 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem388905 : term18 = term19.
Proof. exact (MK_COMB (@lem388896) (@lem388895)). Qed.
Lemma lem388906 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem388907 (m : nat) : (term20 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem388906 m n)). Qed.
Lemma lem388908 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem388909 (m : nat) : (term21 m) = (term21 m).
Proof. exact (MK_COMB (@lem388908) (@lem388907 m)). Qed.
Lemma lem388912 (m : nat) : (term22 m) = (term22 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem388913 (m : nat) : (term23 m) = (term23 m).
Proof. exact (MK_COMB (@lem388912 m) (@lem388909 m)). Qed.
Lemma lem388914 : term24 = term24.
Proof. exact (fun_ext (fun m : nat => @lem388913 m)). Qed.
Lemma lem388915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem388916 : term10 = term10.
Proof. exact (MK_COMB (@lem388915) (@lem388914)). Qed.
Lemma lem388917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem388918 : term9 = term9.
Proof. exact (MK_COMB (@lem388917) (@lem388916)). Qed.
Lemma lem388921 (n : nat) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem388922 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem388921 n)). Qed.
Lemma lem388923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem388924 : term27 = term27.
Proof. exact (MK_COMB (@lem388923) (@lem388922)). Qed.
Lemma lem388925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem388926 : term11 = term11.
Proof. exact (MK_COMB (@lem388925) (@lem388924)). Qed.
Lemma lem388927 : term13 = term13.
Proof. exact (MK_COMB (@lem388926) (@lem388918)). Qed.
Lemma lem388928 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem388929 (P : nat -> Prop) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun n : nat => @lem388928 P n)). Qed.
Lemma lem388930 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem388931 (P : nat -> Prop) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem388930) (@lem388929 P)). Qed.
Lemma lem388932 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem388933 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem388932 P n)). Qed.
Lemma lem388934 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem388935 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem388934) (@lem388933 P)). Qed.
Lemma lem388936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem388937 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem388936) (@lem388935 P)). Qed.
Lemma lem388938 (P : nat -> Prop) : ((term32 P) = (term29 P)) = ((term32 P) = (term29 P)).
Proof. exact (MK_COMB (@lem388937 P) (@lem388931 P)). Qed.
Lemma lem388943 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (eq_refl (term34 P)). Qed.
Lemma lem388944 (P : nat -> Prop) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem388943 P) (@lem388938 P)). Qed.
Lemma lem388945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem388946 (P : nat -> Prop) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem388945) (@lem388944 P)). Qed.
Lemma lem388947 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem388948 (P : nat -> Prop) : (term14 P) = (term14 P).
Proof. exact (MK_COMB (@lem388947) (@lem388946 P)). Qed.
Lemma lem388949 (P : nat -> Prop) : (term15 P) = (term15 P).
Proof. exact (MK_COMB (@lem388948 P) (@lem388927)). Qed.
Lemma lem388950 : term17 = term17.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem388949 P)). Qed.
Lemma lem388951 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem388952 : term19 = term19.
Proof. exact (MK_COMB (@lem388951) (@lem388950)). Qed.
Lemma lem388999 : term18 = term19.
Proof. exact (TRANS (@lem388905) (@lem388952)). Qed.
Lemma lem389000 : term19 = term18.
Proof. exact (SYM (@lem388999)). Qed.
Lemma lem389001 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem389003 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem389006 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem389007 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem389008 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem389007 (term31 P)). Qed.
Lemma lem389009 (P : nat -> Prop) (n : nat) : (term39 P n) = (term30 P n).
Proof. exact (eq_refl (term39 P n)). Qed.
Lemma lem389010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem389012 (P : nat -> Prop) (n : nat) : (term40 P n) = (term41 P n).
Proof. exact (MK_COMB (@lem389010) (@lem389009 P n)). Qed.
Lemma lem389013 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem389012 P n)). Qed.
Lemma lem389014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389015 (P : nat -> Prop) : (term38 P) = (term44 P).
Proof. exact (MK_COMB (@lem389014) (@lem389013 P)). Qed.
Lemma lem389016 (P : nat -> Prop) : (term37 P) = (term44 P).
Proof. exact (TRANS (@lem389008 P) (@lem389015 P)). Qed.
Lemma lem389017 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem389006 P n)). Qed.
Lemma lem389018 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389019 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem389018) (@lem389017 P)). Qed.
Lemma lem389021 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem389022 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem389023 (P : nat -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem389022 (term28 P)). Qed.
Lemma lem389024 (P : nat -> Prop) (n : nat) : (term47 P n) = (P n).
Proof. exact (eq_refl (term47 P n)). Qed.
Lemma lem389025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem389027 (P : nat -> Prop) (n : nat) : (term48 P n) = (term49 P n).
Proof. exact (MK_COMB (@lem389025) (@lem389024 P n)). Qed.
Lemma lem389028 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem389027 P n)). Qed.
Lemma lem389029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389030 (P : nat -> Prop) : (term46 P) = (term36 P).
Proof. exact (MK_COMB (@lem389029) (@lem389028 P)). Qed.
Lemma lem389031 (P : nat -> Prop) : (term45 P) = (term36 P).
Proof. exact (TRANS (@lem389023 P) (@lem389030 P)). Qed.
Lemma lem389032 (P : nat -> Prop) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun n : nat => @lem389021 P n)). Qed.
Lemma lem389033 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389034 (P : nat -> Prop) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem389033) (@lem389032 P)). Qed.
Lemma lem389035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389036 (P : nat -> Prop) : (term52 P) = (term53 P).
Proof. exact (MK_COMB (@lem389035) (@lem389016 P)). Qed.
Lemma lem389037 (P : nat -> Prop) : (term54 P) = (term55 P).
Proof. exact (MK_COMB (@lem389036 P) (@lem389034 P)). Qed.
Lemma lem389038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389039 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (MK_COMB (@lem389038) (@lem389019 P)). Qed.
Lemma lem389040 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (MK_COMB (@lem389039 P) (@lem389031 P)). Qed.
Lemma lem389041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem389042 (P : nat -> Prop) : (term59 P) = (term60 P).
Proof. exact (MK_COMB (@lem389041) (@lem389040 P)). Qed.
Lemma lem389043 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (MK_COMB (@lem389042 P) (@lem389037 P)). Qed.
Lemma lem389044 (P : nat -> Prop) : (term63 P) = (term61 P).
Proof. exact (@lem17646 (term32 P) (term29 P)). Qed.
Lemma lem389045 (P : nat -> Prop) : (term63 P) = (term62 P).
Proof. exact (TRANS (@lem389044 P) (@lem389043 P)). Qed.
Lemma lem389047 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem389048 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem389047 P) (@lem389045 P)). Qed.
Lemma lem389049 (P : nat -> Prop) : (term3 P) = (term65 P).
Proof. exact (@lem17362 (term67 P) ((term32 P) = (term29 P))). Qed.
Lemma lem389050 (P : nat -> Prop) : (term3 P) = (term66 P).
Proof. exact (TRANS (@lem389049 P) (@lem389048 P)). Qed.
Lemma lem389069 {A : Type'} (P : A -> Prop) (Q : Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem389070 (P : nat -> Prop) (Q : Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem389069 nat P Q). Qed.
Lemma lem389071 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem389070 (term31 P) (term36 P)). Qed.
Lemma lem389072 (P : nat -> Prop) (n : nat) : (term39 P n) = (term30 P n).
Proof. exact (eq_refl (term39 P n)). Qed.
Lemma lem389073 (P : nat -> Prop) : (term74 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem389072 P n)). Qed.
Lemma lem389074 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389075 (P : nat -> Prop) : (term75 P) = (term32 P).
Proof. exact (MK_COMB (@lem389074) (@lem389073 P)). Qed.
Lemma lem389076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389077 (P : nat -> Prop) : (term76 P) = (term56 P).
Proof. exact (MK_COMB (@lem389076) (@lem389075 P)). Qed.
Lemma lem389078 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (eq_refl (term36 P)). Qed.
Lemma lem389079 (P : nat -> Prop) : (term72 P) = (term58 P).
Proof. exact (MK_COMB (@lem389077 P) (@lem389078 P)). Qed.
Lemma lem389080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389081 (P : nat -> Prop) : (term77 P) = (term78 P).
Proof. exact (MK_COMB (@lem389080) (@lem389079 P)). Qed.
Lemma lem389082 (P : nat -> Prop) (n : nat) : (term39 P n) = (term30 P n).
Proof. exact (eq_refl (term39 P n)). Qed.
Lemma lem389083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389084 (P : nat -> Prop) (n : nat) : (term79 P n) = (term80 P n).
Proof. exact (MK_COMB (@lem389083) (@lem389082 P n)). Qed.
Lemma lem389085 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (eq_refl (term36 P)). Qed.
Lemma lem389086 (n : nat) (P : nat -> Prop) : (term81 n P) = (term82 n P).
Proof. exact (MK_COMB (@lem389084 P n) (@lem389085 P)). Qed.
Lemma lem389087 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (fun_ext (fun n : nat => @lem389086 n P)). Qed.
Lemma lem389088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389089 (P : nat -> Prop) : (term73 P) = (term85 P).
Proof. exact (MK_COMB (@lem389088) (@lem389087 P)). Qed.
Lemma lem389090 (P : nat -> Prop) : ((term72 P) = (term73 P)) = ((term58 P) = (term85 P)).
Proof. exact (MK_COMB (@lem389081 P) (@lem389089 P)). Qed.
Lemma lem389091 (P : nat -> Prop) : (term58 P) = (term85 P).
Proof. exact (EQ_MP (@lem389090 P) (@lem389071 P)). Qed.
Lemma lem389092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem389093 (P : nat -> Prop) : (term60 P) = (term86 P).
Proof. exact (MK_COMB (@lem389092) (@lem389091 P)). Qed.
Lemma lem389095 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem389096 (P : Prop) (Q : nat -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem389095 nat P Q). Qed.
Lemma lem389097 (P : nat -> Prop) : (term55 P) = (term91 P).
Proof. exact (@lem389096 (term44 P) P). Qed.
Lemma lem389098 (P : nat -> Prop) : (term62 P) = (term92 P).
Proof. exact (MK_COMB (@lem389093 P) (@lem389097 P)). Qed.
Lemma lem389100 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem389101 (P : nat -> Prop) (Q : nat -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem389100 nat P Q). Qed.
Lemma lem389102 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem389101 (term84 P) (term99 P)). Qed.
Lemma lem389103 (n : nat) (P : nat -> Prop) : (term100 P n) = (term82 n P).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem389104 (P : nat -> Prop) : (term101 P) = (term84 P).
Proof. exact (fun_ext (fun n : nat => @lem389103 n P)). Qed.
Lemma lem389105 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389106 (P : nat -> Prop) : (term102 P) = (term85 P).
Proof. exact (MK_COMB (@lem389105) (@lem389104 P)). Qed.
Lemma lem389107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem389108 (P : nat -> Prop) : (term103 P) = (term86 P).
Proof. exact (MK_COMB (@lem389107) (@lem389106 P)). Qed.
Lemma lem389109 (P : nat -> Prop) (n : nat) : (term104 P n) = (term105 P n).
Proof. exact (eq_refl (term104 P n)). Qed.
Lemma lem389110 (P : nat -> Prop) : (term106 P) = (term99 P).
Proof. exact (fun_ext (fun n : nat => @lem389109 P n)). Qed.
Lemma lem389111 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389112 (P : nat -> Prop) : (term107 P) = (term91 P).
Proof. exact (MK_COMB (@lem389111) (@lem389110 P)). Qed.
Lemma lem389113 (P : nat -> Prop) : (term97 P) = (term92 P).
Proof. exact (MK_COMB (@lem389108 P) (@lem389112 P)). Qed.
Lemma lem389114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389115 (P : nat -> Prop) : (term108 P) = (term109 P).
Proof. exact (MK_COMB (@lem389114) (@lem389113 P)). Qed.
Lemma lem389116 (n : nat) (P : nat -> Prop) : (term100 P n) = (term82 n P).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem389117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem389118 (n : nat) (P : nat -> Prop) : (term110 P n) = (term111 n P).
Proof. exact (MK_COMB (@lem389117) (@lem389116 n P)). Qed.
Lemma lem389119 (P : nat -> Prop) (n : nat) : (term104 P n) = (term105 P n).
Proof. exact (eq_refl (term104 P n)). Qed.
Lemma lem389120 (P : nat -> Prop) (n : nat) : (term112 P n) = (term113 P n).
Proof. exact (MK_COMB (@lem389118 n P) (@lem389119 P n)). Qed.
Lemma lem389121 (P : nat -> Prop) : (term114 P) = (term115 P).
Proof. exact (fun_ext (fun n : nat => @lem389120 P n)). Qed.
Lemma lem389122 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389123 (P : nat -> Prop) : (term98 P) = (term116 P).
Proof. exact (MK_COMB (@lem389122) (@lem389121 P)). Qed.
Lemma lem389124 (P : nat -> Prop) : ((term97 P) = (term98 P)) = ((term92 P) = (term116 P)).
Proof. exact (MK_COMB (@lem389115 P) (@lem389123 P)). Qed.
Lemma lem389125 (P : nat -> Prop) : (term92 P) = (term116 P).
Proof. exact (EQ_MP (@lem389124 P) (@lem389102 P)). Qed.
Lemma lem389126 (P : nat -> Prop) : (term62 P) = (term116 P).
Proof. exact (TRANS (@lem389098 P) (@lem389125 P)). Qed.
Lemma lem389127 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem389128 (P : nat -> Prop) : (term66 P) = (term117 P).
Proof. exact (MK_COMB (@lem389127 P) (@lem389126 P)). Qed.
Lemma lem389130 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem389131 (P : Prop) (Q : nat -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem389130 nat P Q). Qed.
Lemma lem389132 (P : nat -> Prop) : (term118 P) = (term119 P).
Proof. exact (@lem389131 (term67 P) (term115 P)). Qed.
Lemma lem389133 (P : nat -> Prop) (n : nat) : (term120 P n) = (term113 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem389134 (P : nat -> Prop) : (term121 P) = (term115 P).
Proof. exact (fun_ext (fun n : nat => @lem389133 P n)). Qed.
Lemma lem389135 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389136 (P : nat -> Prop) : (term122 P) = (term116 P).
Proof. exact (MK_COMB (@lem389135) (@lem389134 P)). Qed.
Lemma lem389137 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem389138 (P : nat -> Prop) : (term118 P) = (term117 P).
Proof. exact (MK_COMB (@lem389137 P) (@lem389136 P)). Qed.
Lemma lem389139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389140 (P : nat -> Prop) : (term123 P) = (term124 P).
Proof. exact (MK_COMB (@lem389139) (@lem389138 P)). Qed.
Lemma lem389141 (P : nat -> Prop) (n : nat) : (term120 P n) = (term113 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem389142 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem389143 (P : nat -> Prop) (n : nat) : (term125 P n) = (term126 P n).
Proof. exact (MK_COMB (@lem389142 P) (@lem389141 P n)). Qed.
Lemma lem389144 (P : nat -> Prop) : (term127 P) = (term128 P).
Proof. exact (fun_ext (fun n : nat => @lem389143 P n)). Qed.
Lemma lem389145 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389146 (P : nat -> Prop) : (term119 P) = (term129 P).
Proof. exact (MK_COMB (@lem389145) (@lem389144 P)). Qed.
Lemma lem389147 (P : nat -> Prop) : ((term118 P) = (term119 P)) = ((term117 P) = (term129 P)).
Proof. exact (MK_COMB (@lem389140 P) (@lem389146 P)). Qed.
Lemma lem389148 (P : nat -> Prop) : (term117 P) = (term129 P).
Proof. exact (EQ_MP (@lem389147 P) (@lem389132 P)). Qed.
Lemma lem389150 (P : nat -> Prop) : (term66 P) = (term129 P).
Proof. exact (TRANS (@lem389128 P) (@lem389148 P)). Qed.
Lemma lem389151 (P : nat -> Prop) : (term3 P) = (term129 P).
Proof. exact (TRANS (@lem389050 P) (@lem389150 P)). Qed.
Lemma lem389152 (P : nat -> Prop) (h1 : term3 P) : term129 P.
Proof. exact (EQ_MP (@lem389151 P) (@lem389001 P h1)). Qed.
Lemma lem389167 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem389168 (m : nat) : (term20 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem389167 m n)). Qed.
Lemma lem389169 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389170 (m : nat) : (term21 m) = (term21 m).
Proof. exact (MK_COMB (@lem389169) (@lem389168 m)). Qed.
Lemma lem389172 (m : nat) : (term22 m) = (term22 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem389173 (m : nat) : (term23 m) = (term23 m).
Proof. exact (MK_COMB (@lem389172 m) (@lem389170 m)). Qed.
Lemma lem389174 : term24 = term24.
Proof. exact (fun_ext (fun m : nat => @lem389173 m)). Qed.
Lemma lem389175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389176 : term10 = term10.
Proof. exact (MK_COMB (@lem389175) (@lem389174)). Qed.
Lemma lem389231 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem389232 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem389231 nat P Q). Qed.
Lemma lem389233 (m : nat) : (term134 m) = (term135 m).
Proof. exact (@lem389232 (m = (NUMERAL 0)) (term20 m)). Qed.
Lemma lem389234 (m : nat) (n : nat) : (term136 m n) = (m = (S n)).
Proof. exact (eq_refl (term136 m n)). Qed.
Lemma lem389235 (m : nat) : (term137 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem389234 m n)). Qed.
Lemma lem389236 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389237 (m : nat) : (term138 m) = (term21 m).
Proof. exact (MK_COMB (@lem389236) (@lem389235 m)). Qed.
Lemma lem389238 (m : nat) : (term22 m) = (term22 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem389239 (m : nat) : (term134 m) = (term23 m).
Proof. exact (MK_COMB (@lem389238 m) (@lem389237 m)). Qed.
Lemma lem389240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389241 (m : nat) : (term139 m) = (term140 m).
Proof. exact (MK_COMB (@lem389240) (@lem389239 m)). Qed.
Lemma lem389242 (m : nat) (n : nat) : (term136 m n) = (m = (S n)).
Proof. exact (eq_refl (term136 m n)). Qed.
Lemma lem389243 (m : nat) : (term22 m) = (term22 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem389244 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (MK_COMB (@lem389243 m) (@lem389242 m n)). Qed.
Lemma lem389245 (m : nat) : (term143 m) = (term144 m).
Proof. exact (fun_ext (fun n : nat => @lem389244 m n)). Qed.
Lemma lem389246 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389247 (m : nat) : (term135 m) = (term145 m).
Proof. exact (MK_COMB (@lem389246) (@lem389245 m)). Qed.
Lemma lem389248 (m : nat) : ((term134 m) = (term135 m)) = ((term23 m) = (term145 m)).
Proof. exact (MK_COMB (@lem389241 m) (@lem389247 m)). Qed.
Lemma lem389249 (m : nat) : (term23 m) = (term145 m).
Proof. exact (EQ_MP (@lem389248 m) (@lem389233 m)). Qed.
Lemma lem389250 : term24 = term146.
Proof. exact (fun_ext (fun m : nat => @lem389249 m)). Qed.
Lemma lem389251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389252 : term10 = term147.
Proof. exact (MK_COMB (@lem389251) (@lem389250)). Qed.
Lemma lem389254 {A B : Type'} (P : type1413 A B) : (term148 A B P) = (term149 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem389255 (P : type1605) : (term150 P) = (term151 P).
Proof. exact (@lem389254 nat nat P). Qed.
Lemma lem389256 : term152 = term153.
Proof. exact (@lem389255 term154). Qed.
Lemma lem389257 (m : nat) : (term155 m) = (term144 m).
Proof. exact (eq_refl (term155 m)). Qed.
Lemma lem389258 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem389259 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem389257 m) (@lem389258 n)). Qed.
Lemma lem389260 (m : nat) (n : nat) : (term157 m n) = (term142 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem389261 (m : nat) (n : nat) : (term156 m n) = (term142 m n).
Proof. exact (TRANS (@lem389259 m n) (@lem389260 m n)). Qed.
Lemma lem389262 (m : nat) : (term158 m) = (term144 m).
Proof. exact (fun_ext (fun n : nat => @lem389261 m n)). Qed.
Lemma lem389263 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem389264 (m : nat) : (term159 m) = (term145 m).
Proof. exact (MK_COMB (@lem389263) (@lem389262 m)). Qed.
Lemma lem389265 : term160 = term146.
Proof. exact (fun_ext (fun m : nat => @lem389264 m)). Qed.
Lemma lem389266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389267 : term152 = term147.
Proof. exact (MK_COMB (@lem389266) (@lem389265)). Qed.
Lemma lem389268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389269 : term161 = term162.
Proof. exact (MK_COMB (@lem389268) (@lem389267)). Qed.
Lemma lem389270 (m : nat) : (term155 m) = (term144 m).
Proof. exact (eq_refl (term155 m)). Qed.
Lemma lem389271 (n : nat -> nat) (m : nat) : (n m) = (n m).
Proof. exact (eq_refl (n m)). Qed.
Lemma lem389272 (n : nat -> nat) (m : nat) : (term163 n m) = (term164 n m).
Proof. exact (MK_COMB (@lem389270 m) (@lem389271 n m)). Qed.
Lemma lem389273 (n : nat -> nat) (m : nat) : (term164 n m) = (term165 n m).
Proof. exact (eq_refl (term164 n m)). Qed.
Lemma lem389274 (n : nat -> nat) (m : nat) : (term163 n m) = (term165 n m).
Proof. exact (TRANS (@lem389272 n m) (@lem389273 n m)). Qed.
Lemma lem389275 (n : nat -> nat) : (term166 n) = (term167 n).
Proof. exact (fun_ext (fun m : nat => @lem389274 n m)). Qed.
Lemma lem389276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389277 (n : nat -> nat) : (term168 n) = (term169 n).
Proof. exact (MK_COMB (@lem389276) (@lem389275 n)). Qed.
Lemma lem389278 : term170 = term171.
Proof. exact (fun_ext (fun n : nat -> nat => @lem389277 n)). Qed.
Lemma lem389279 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem389280 : term153 = term172.
Proof. exact (MK_COMB (@lem389279) (@lem389278)). Qed.
Lemma lem389281 : (term152 = term153) = (term147 = term172).
Proof. exact (MK_COMB (@lem389269) (@lem389280)). Qed.
Lemma lem389282 : term147 = term172.
Proof. exact (EQ_MP (@lem389281) (@lem389256)). Qed.
Lemma lem389284 : term10 = term172.
Proof. exact (TRANS (@lem389252) (@lem389282)). Qed.
Lemma lem389285 : term10 = term172.
Proof. exact (TRANS (@lem389176) (@lem389284)). Qed.
Lemma lem389286 (h1 : term10) : term172.
Proof. exact (EQ_MP (@lem389285) (@lem389003 h1)). Qed.
Lemma lem389287 (n : nat -> nat) (h1 : term169 n) : term169 n.
Proof. exact (h1). Qed.
Lemma lem389288 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term126 P n'.
Proof. exact (h1). Qed.
Lemma lem389322 (n : nat -> nat) (m : nat) : (term165 n m) = (term165 n m).
Proof. exact (eq_refl (term165 n m)). Qed.
Lemma lem389323 (n : nat -> nat) : (term167 n) = (term167 n).
Proof. exact (fun_ext (fun m : nat => @lem389322 n m)). Qed.
Lemma lem389324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389325 (n : nat -> nat) : (term169 n) = (term169 n).
Proof. exact (MK_COMB (@lem389324) (@lem389323 n)). Qed.
Lemma lem389326 (n : nat -> nat) (h1 : term169 n) : term169 n.
Proof. exact (EQ_MP (@lem389325 n) (@lem389287 n h1)). Qed.
Lemma lem389329 (P : nat -> Prop) (n' : nat) : (P n') = (P n').
Proof. exact (eq_refl (P n')). Qed.
Lemma lem389336 (P : nat -> Prop) (n : nat) : (term41 P n) = (term41 P n).
Proof. exact (eq_refl (term41 P n)). Qed.
Lemma lem389337 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem389336 P n)). Qed.
Lemma lem389338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389339 (P : nat -> Prop) : (term44 P) = (term44 P).
Proof. exact (MK_COMB (@lem389338) (@lem389337 P)). Qed.
Lemma lem389340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389341 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (MK_COMB (@lem389340) (@lem389339 P)). Qed.
Lemma lem389342 (P : nat -> Prop) (n' : nat) : (term105 P n') = (term105 P n').
Proof. exact (MK_COMB (@lem389341 P) (@lem389329 P n')). Qed.
Lemma lem389347 (P : nat -> Prop) (n : nat) : (term49 P n) = (term49 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem389348 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem389347 P n)). Qed.
Lemma lem389349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389350 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem389349) (@lem389348 P)). Qed.
Lemma lem389357 (P : nat -> Prop) (n' : nat) : (term80 P n') = (term80 P n').
Proof. exact (eq_refl (term80 P n')). Qed.
Lemma lem389358 (n' : nat) (P : nat -> Prop) : (term82 n' P) = (term82 n' P).
Proof. exact (MK_COMB (@lem389357 P n') (@lem389350 P)). Qed.
Lemma lem389359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem389360 (n' : nat) (P : nat -> Prop) : (term111 n' P) = (term111 n' P).
Proof. exact (MK_COMB (@lem389359) (@lem389358 n' P)). Qed.
Lemma lem389361 (P : nat -> Prop) (n' : nat) : (term113 P n') = (term113 P n').
Proof. exact (MK_COMB (@lem389360 n' P) (@lem389342 P n')). Qed.
Lemma lem389370 (P : nat -> Prop) : (term64 P) = (term64 P).
Proof. exact (eq_refl (term64 P)). Qed.
Lemma lem389371 (P : nat -> Prop) (n' : nat) : (term126 P n') = (term126 P n').
Proof. exact (MK_COMB (@lem389370 P) (@lem389361 P n')). Qed.
Lemma lem389372 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term126 P n'.
Proof. exact (EQ_MP (@lem389371 P n') (@lem389288 P n' h1)). Qed.
Lemma lem389373 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term113 P n'.
Proof. exact (proj2 (@lem389372 P n' h1)). Qed.
Lemma lem389375 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term82 n' P.
Proof. exact (h1). Qed.
Lemma lem389376 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term105 P n'.
Proof. exact (h1). Qed.
Lemma lem389377 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term36 P.
Proof. exact (proj2 (@lem389375 n' P h1)). Qed.
Lemma lem389380 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term44 P.
Proof. exact (proj1 (@lem389376 P n' h1)). Qed.
Lemma lem389410 (P : nat -> Prop) (n : nat) : (term49 P n) = (term49 P n).
Proof. exact (eq_refl (term49 P n)). Qed.
Lemma lem389411 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (fun_ext (fun n : nat => @lem389410 P n)). Qed.
Lemma lem389412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389414 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem389412) (@lem389411 P)). Qed.
Lemma lem389415 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term36 P.
Proof. exact (EQ_MP (@lem389414 P) (@lem389377 n' P h1)). Qed.
Lemma lem389430 (n : nat -> nat) (m : nat) : (term165 n m) = (term165 n m).
Proof. exact (eq_refl (term165 n m)). Qed.
Lemma lem389431 (n : nat -> nat) : (term167 n) = (term167 n).
Proof. exact (fun_ext (fun m : nat => @lem389430 n m)). Qed.
Lemma lem389432 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389434 (n : nat -> nat) : (term169 n) = (term169 n).
Proof. exact (MK_COMB (@lem389432) (@lem389431 n)). Qed.
Lemma lem389435 (n : nat -> nat) (h1 : term169 n) : term169 n.
Proof. exact (EQ_MP (@lem389434 n) (@lem389326 n h1)). Qed.
Lemma lem389441 (P : nat -> Prop) (n : nat) : (term41 P n) = (term41 P n).
Proof. exact (eq_refl (term41 P n)). Qed.
Lemma lem389442 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem389441 P n)). Qed.
Lemma lem389443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389445 (P : nat -> Prop) : (term44 P) = (term44 P).
Proof. exact (MK_COMB (@lem389443) (@lem389442 P)). Qed.
Lemma lem389446 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term44 P.
Proof. exact (EQ_MP (@lem389445 P) (@lem389380 P n' h1)). Qed.
Lemma lem389457 (_8186 : nat) (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term173 P _8186.
Proof. exact (@lem389415 n' P h1 _8186). Qed.
Lemma lem389458 (P : nat -> Prop) (_8186 : nat) : (term173 P _8186) = (term49 P _8186).
Proof. exact (eq_refl (term173 P _8186)). Qed.
Lemma lem389463 (_8188 : nat) (n : nat -> nat) (h1 : term169 n) : term174 n _8188.
Proof. exact (@lem389435 n h1 _8188). Qed.
Lemma lem389464 (n : nat -> nat) (_8188 : nat) : (term174 n _8188) = (term165 n _8188).
Proof. exact (eq_refl (term174 n _8188)). Qed.
Lemma lem389466 (_8189 : nat) (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term175 P _8189.
Proof. exact (@lem389446 P n' h1 _8189). Qed.
Lemma lem389467 (P : nat -> Prop) (_8189 : nat) : (term175 P _8189) = (term41 P _8189).
Proof. exact (eq_refl (term175 P _8189)). Qed.
Lemma lem389482 (_8186 : nat) (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term49 P _8186.
Proof. exact (EQ_MP (@lem389458 P _8186) (@lem389457 _8186 n' P h1)). Qed.
Lemma lem389490 (_8188 : nat) (n : nat -> nat) (h1 : term169 n) : term165 n _8188.
Proof. exact (EQ_MP (@lem389464 n _8188) (@lem389463 _8188 n h1)). Qed.
Lemma lem389494 (_8189 : nat) (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term41 P _8189.
Proof. exact (EQ_MP (@lem389467 P _8189) (@lem389466 _8189 P n' h1)). Qed.
Lemma lem389536 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term30 P n'.
Proof. exact (proj1 (@lem389375 n' P h1)). Qed.
Lemma lem389537 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term176 P n'.
Proof. exact (fun h0 : term41 P n' => @lem389536 n' P h1). Qed.
Lemma lem389539 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389540 (P : nat -> Prop) (n' : nat) : (term176 P n') = (term30 P n').
Proof. exact (@lem389539 (term30 P n')). Qed.
Lemma lem389541 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term30 P n'.
Proof. exact (EQ_MP (@lem389540 P n') (@lem389537 n' P h1)). Qed.
Lemma lem389544 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem389546 (P : nat -> Prop) (_8186 : nat) : (term49 P _8186) = (term178 P _8186).
Proof. exact (@lem389544 (P _8186)). Qed.
Lemma lem389549 (_8186 : nat) (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term178 P _8186.
Proof. exact (EQ_MP (@lem389546 P _8186) (@lem389482 _8186 n' P h1)). Qed.
Lemma lem389550 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term179 P n'.
Proof. exact (@lem389549 (S n') n' P h1). Qed.
Lemma lem389553 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : False.
Proof. exact (@lem389550 n' P h1 (@lem389541 n' P h1)). Qed.
Lemma lem389554 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : term180.
Proof. exact (fun h0 : ~ False => @lem389553 n' P h1). Qed.
Lemma lem389556 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389557 : term180 = False.
Proof. exact (@lem389556 False). Qed.
Lemma lem389558 (n' : nat) (P : nat -> Prop) (h1 : term82 n' P) : False.
Proof. exact (EQ_MP (@lem389557) (@lem389554 n' P h1)). Qed.
Lemma lem389559 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem389560 (_8198 : nat) (_8199 : nat) (h1 : _8198 = _8199) : _8198 = _8199.
Proof. exact (h1). Qed.
Lemma lem389561 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) (h1 : _8198 = _8199) : (P _8198) = (P _8199).
Proof. exact (MK_COMB (@lem389559 P) (@lem389560 _8198 _8199 h1)). Qed.
Lemma lem389563 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem389564 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : term182 _8199 P _8198.
Proof. exact (@lem389563 (P _8199) (P _8198)). Qed.
Lemma lem389565 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) (h1 : _8198 = _8199) : term183 _8199 P _8198.
Proof. exact (@lem389564 _8199 P _8198 (@lem389561 P _8198 _8199 h1)). Qed.
Lemma lem389566 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : term184 _8199 P _8198.
Proof. exact (fun h0 : _8198 = _8199 => @lem389565 P _8198 _8199 h0). Qed.
Lemma lem389568 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem389569 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term184 _8199 P _8198) = (term186 _8199 P _8198).
Proof. exact (@lem389568 (_8198 = _8199) (term183 _8199 P _8198)). Qed.
Lemma lem389570 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : term186 _8199 P _8198.
Proof. exact (EQ_MP (@lem389569 _8199 P _8198) (@lem389566 _8199 P _8198)). Qed.
Lemma lem389598 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term67 P.
Proof. exact (proj1 (@lem389372 P n' h1)). Qed.
Lemma lem389599 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term187 P.
Proof. exact (fun h0 : term188 P => @lem389598 P n' h1). Qed.
Lemma lem389601 (p : Prop) : (term189 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem389602 (P : nat -> Prop) : (term187 P) = (term67 P).
Proof. exact (@lem389601 (term188 P)). Qed.
Lemma lem389603 (P : nat -> Prop) (n' : nat) (h1 : term126 P n') : term67 P.
Proof. exact (EQ_MP (@lem389602 P) (@lem389599 P n' h1)). Qed.
Lemma lem389605 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : P n'.
Proof. exact (proj2 (@lem389376 P n' h1)). Qed.
Lemma lem389606 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term190 P n'.
Proof. exact (fun h0 : term49 P n' => @lem389605 P n' h1). Qed.
Lemma lem389608 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389609 (P : nat -> Prop) (n' : nat) : (term190 P n') = (P n').
Proof. exact (@lem389608 (P n')). Qed.
Lemma lem389610 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : P n'.
Proof. exact (EQ_MP (@lem389609 P n') (@lem389606 P n' h1)). Qed.
Lemma lem389612 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem389613 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term186 _8199 P _8198) = (term192 P _8198 _8199).
Proof. exact (@lem389612 (term183 _8199 P _8198) (term193 _8198 _8199)). Qed.
Lemma lem389615 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem389616 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term196 _8199 P _8198) = (term197 _8199 P _8198).
Proof. exact (@lem389615 (P _8199) (term49 P _8198)). Qed.
Lemma lem389618 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem389619 (P : nat -> Prop) (_8198 : nat) : (term199 P _8198) = (P _8198).
Proof. exact (@lem389618 (P _8198)). Qed.
Lemma lem389620 (P : nat -> Prop) (_8199 : nat) : (term200 P _8199) = (term200 P _8199).
Proof. exact (eq_refl (term200 P _8199)). Qed.
Lemma lem389621 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term197 _8199 P _8198) = (term201 _8199 P _8198).
Proof. exact (MK_COMB (@lem389620 P _8199) (@lem389619 P _8198)). Qed.
Lemma lem389622 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term196 _8199 P _8198) = (term201 _8199 P _8198).
Proof. exact (TRANS (@lem389616 _8199 P _8198) (@lem389621 _8199 P _8198)). Qed.
Lemma lem389623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389624 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term202 _8199 P _8198) = (term203 _8199 P _8198).
Proof. exact (MK_COMB (@lem389623) (@lem389622 _8199 P _8198)). Qed.
Lemma lem389625 (_8198 : nat) (_8199 : nat) : (term193 _8198 _8199) = (term193 _8198 _8199).
Proof. exact (eq_refl (term193 _8198 _8199)). Qed.
Lemma lem389626 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term192 P _8198 _8199) = (term204 P _8198 _8199).
Proof. exact (MK_COMB (@lem389624 _8199 P _8198) (@lem389625 _8198 _8199)). Qed.
Lemma lem389627 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term186 _8199 P _8198) = (term204 P _8198 _8199).
Proof. exact (TRANS (@lem389613 P _8198 _8199) (@lem389626 P _8198 _8199)). Qed.
Lemma lem389629 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') (h2 : term126 P n') : term205 P n'.
Proof. exact (conj (@lem389603 P n' h2) (@lem389610 P n' h1)). Qed.
Lemma lem389631 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : term204 P _8198 _8199.
Proof. exact (EQ_MP (@lem389627 P _8198 _8199) (@lem389570 _8199 P _8198)). Qed.
Lemma lem389632 (P : nat -> Prop) (n' : nat) : term206 P n'.
Proof. exact (@lem389631 P n' (NUMERAL 0)). Qed.
Lemma lem389635 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') (h2 : term126 P n') : term207 n'.
Proof. exact (@lem389632 P n' (@lem389629 P n' h1 h2)). Qed.
Lemma lem389636 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') (h2 : term126 P n') : term208 n'.
Proof. exact (fun h0 : n' = (NUMERAL 0) => @lem389635 P n' h1 h2). Qed.
Lemma lem389638 (p : Prop) : (term189 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem389639 (n' : nat) : (term208 n') = (term207 n').
Proof. exact (@lem389638 (n' = (NUMERAL 0))). Qed.
Lemma lem389640 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') (h2 : term126 P n') : term207 n'.
Proof. exact (EQ_MP (@lem389639 n') (@lem389636 P n' h1 h2)). Qed.
Lemma lem389655 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem389656 (n : nat -> nat) (_8188 : nat) : (term209 n _8188) = (term165 n _8188).
Proof. exact (@lem389655 (_8188 = (NUMERAL 0)) (_8188 = (term210 n _8188))). Qed.
Lemma lem389666 (n : nat -> nat) (_8188 : nat) : (term211 n _8188) = (term211 n _8188).
Proof. exact (eq_refl (term211 n _8188)). Qed.
Lemma lem389667 (n : nat -> nat) (_8188 : nat) : ((term165 n _8188) = (term209 n _8188)) = ((term165 n _8188) = (term165 n _8188)).
Proof. exact (MK_COMB (@lem389666 n _8188) (@lem389656 n _8188)). Qed.
Lemma lem389669 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem389670 (x : Prop) : (x = x) = True.
Proof. exact (@lem389669 Prop x). Qed.
Lemma lem389671 (n : nat -> nat) (_8188 : nat) : ((term165 n _8188) = (term165 n _8188)) = True.
Proof. exact (@lem389670 (term165 n _8188)). Qed.
Lemma lem389672 (n : nat -> nat) (_8188 : nat) : ((term165 n _8188) = (term209 n _8188)) = True.
Proof. exact (TRANS (@lem389667 n _8188) (@lem389671 n _8188)). Qed.
Lemma lem389673 (n : nat -> nat) (_8188 : nat) : True = ((term165 n _8188) = (term209 n _8188)).
Proof. exact (SYM (@lem389672 n _8188)). Qed.
Lemma lem389674 (n : nat -> nat) (_8188 : nat) : (term165 n _8188) = (term209 n _8188).
Proof. exact (EQ_MP (@lem389673 n _8188) (@lem0)). Qed.
Lemma lem389675 (_8188 : nat) (n : nat -> nat) (h1 : term169 n) : term209 n _8188.
Proof. exact (EQ_MP (@lem389674 n _8188) (@lem389490 _8188 n h1)). Qed.
Lemma lem389677 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem389680 (n : nat -> nat) (_8188 : nat) : (term209 n _8188) = (term212 n _8188).
Proof. exact (@lem389677 (_8188 = (NUMERAL 0)) (_8188 = (term210 n _8188))). Qed.
Lemma lem389683 (_8188 : nat) (n : nat -> nat) (h1 : term169 n) : term212 n _8188.
Proof. exact (EQ_MP (@lem389680 n _8188) (@lem389675 _8188 n h1)). Qed.
Lemma lem389684 (n' : nat) (n : nat -> nat) (h1 : term169 n) : term212 n n'.
Proof. exact (@lem389683 n' n h1). Qed.
Lemma lem389687 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : n' = (term210 n n').
Proof. exact (@lem389684 n' n h1 (@lem389640 P n' h2 h3)). Qed.
Lemma lem389688 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term213 n n'.
Proof. exact (fun h0 : term214 n n' => @lem389687 n P n' h1 h2 h3). Qed.
Lemma lem389690 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389691 (n : nat -> nat) (n' : nat) : (term213 n n') = (n' = (term210 n n')).
Proof. exact (@lem389690 (n' = (term210 n n'))). Qed.
Lemma lem389692 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : n' = (term210 n n').
Proof. exact (EQ_MP (@lem389691 n n') (@lem389688 n P n' h1 h2 h3)). Qed.
Lemma lem389694 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : P n'.
Proof. exact (proj2 (@lem389376 P n' h1)). Qed.
Lemma lem389695 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term190 P n'.
Proof. exact (fun h0 : term49 P n' => @lem389694 P n' h1). Qed.
Lemma lem389697 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389698 (P : nat -> Prop) (n' : nat) : (term190 P n') = (P n').
Proof. exact (@lem389697 (P n')). Qed.
Lemma lem389699 (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : P n'.
Proof. exact (EQ_MP (@lem389698 P n') (@lem389695 P n' h1)). Qed.
Lemma lem389705 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem389706 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term186 _8199 P _8198) = (term216 _8199 P _8198).
Proof. exact (@lem389705 (P _8199) (term193 _8198 _8199) (term49 P _8198)). Qed.
Lemma lem389720 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem389721 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term217 _8199 P _8198) = (term218 P _8198 _8199).
Proof. exact (@lem389720 (term49 P _8198) (term193 _8198 _8199)). Qed.
Lemma lem389729 (P : nat -> Prop) (_8199 : nat) : (term219 P _8199) = (term219 P _8199).
Proof. exact (eq_refl (term219 P _8199)). Qed.
Lemma lem389730 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term216 _8199 P _8198) = (term220 P _8198 _8199).
Proof. exact (MK_COMB (@lem389729 P _8199) (@lem389721 P _8198 _8199)). Qed.
Lemma lem389741 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term186 _8199 P _8198) = (term220 P _8198 _8199).
Proof. exact (TRANS (@lem389706 _8199 P _8198) (@lem389730 P _8198 _8199)). Qed.
Lemma lem389742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem389743 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term221 _8199 P _8198) = (term222 P _8198 _8199).
Proof. exact (MK_COMB (@lem389742) (@lem389741 P _8198 _8199)). Qed.
Lemma lem389757 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem389758 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term217 _8199 P _8198) = (term218 P _8198 _8199).
Proof. exact (@lem389757 (term49 P _8198) (term193 _8198 _8199)). Qed.
Lemma lem389766 (P : nat -> Prop) (_8199 : nat) : (term219 P _8199) = (term219 P _8199).
Proof. exact (eq_refl (term219 P _8199)). Qed.
Lemma lem389767 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : (term216 _8199 P _8198) = (term220 P _8198 _8199).
Proof. exact (MK_COMB (@lem389766 P _8199) (@lem389758 P _8198 _8199)). Qed.
Lemma lem389778 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : ((term186 _8199 P _8198) = (term216 _8199 P _8198)) = ((term220 P _8198 _8199) = (term220 P _8198 _8199)).
Proof. exact (MK_COMB (@lem389743 P _8198 _8199) (@lem389767 P _8198 _8199)). Qed.
Lemma lem389780 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem389781 (x : Prop) : (x = x) = True.
Proof. exact (@lem389780 Prop x). Qed.
Lemma lem389782 (P : nat -> Prop) (_8198 : nat) (_8199 : nat) : ((term220 P _8198 _8199) = (term220 P _8198 _8199)) = True.
Proof. exact (@lem389781 (term220 P _8198 _8199)). Qed.
Lemma lem389783 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : ((term186 _8199 P _8198) = (term216 _8199 P _8198)) = True.
Proof. exact (TRANS (@lem389778 P _8198 _8199) (@lem389782 P _8198 _8199)). Qed.
Lemma lem389784 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : True = ((term186 _8199 P _8198) = (term216 _8199 P _8198)).
Proof. exact (SYM (@lem389783 _8199 P _8198)). Qed.
Lemma lem389785 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term186 _8199 P _8198) = (term216 _8199 P _8198).
Proof. exact (EQ_MP (@lem389784 _8199 P _8198) (@lem0)). Qed.
Lemma lem389786 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : term216 _8199 P _8198.
Proof. exact (EQ_MP (@lem389785 _8199 P _8198) (@lem389570 _8199 P _8198)). Qed.
Lemma lem389788 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem389789 (_8198 : nat) (P : nat -> Prop) (_8199 : nat) : (term216 _8199 P _8198) = (term223 _8198 P _8199).
Proof. exact (@lem389788 (term217 _8199 P _8198) (P _8199)). Qed.
Lemma lem389791 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem389792 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term224 _8199 P _8198) = (term225 _8199 P _8198).
Proof. exact (@lem389791 (term193 _8198 _8199) (term49 P _8198)). Qed.
Lemma lem389794 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem389795 (_8198 : nat) (_8199 : nat) : (term226 _8198 _8199) = (_8198 = _8199).
Proof. exact (@lem389794 (_8198 = _8199)). Qed.
Lemma lem389796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389797 (_8198 : nat) (_8199 : nat) : (term227 _8198 _8199) = (term228 _8198 _8199).
Proof. exact (MK_COMB (@lem389796) (@lem389795 _8198 _8199)). Qed.
Lemma lem389799 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem389800 (P : nat -> Prop) (_8198 : nat) : (term199 P _8198) = (P _8198).
Proof. exact (@lem389799 (P _8198)). Qed.
Lemma lem389801 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term225 _8199 P _8198) = (term229 _8199 P _8198).
Proof. exact (MK_COMB (@lem389797 _8198 _8199) (@lem389800 P _8198)). Qed.
Lemma lem389802 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term224 _8199 P _8198) = (term229 _8199 P _8198).
Proof. exact (TRANS (@lem389792 _8199 P _8198) (@lem389801 _8199 P _8198)). Qed.
Lemma lem389803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389804 (_8199 : nat) (P : nat -> Prop) (_8198 : nat) : (term230 _8199 P _8198) = (term231 _8199 P _8198).
Proof. exact (MK_COMB (@lem389803) (@lem389802 _8199 P _8198)). Qed.
Lemma lem389805 (P : nat -> Prop) (_8199 : nat) : (P _8199) = (P _8199).
Proof. exact (eq_refl (P _8199)). Qed.
Lemma lem389806 (_8198 : nat) (P : nat -> Prop) (_8199 : nat) : (term223 _8198 P _8199) = (term232 _8198 P _8199).
Proof. exact (MK_COMB (@lem389804 _8199 P _8198) (@lem389805 P _8199)). Qed.
Lemma lem389807 (_8198 : nat) (P : nat -> Prop) (_8199 : nat) : (term216 _8199 P _8198) = (term232 _8198 P _8199).
Proof. exact (TRANS (@lem389789 _8198 P _8199) (@lem389806 _8198 P _8199)). Qed.
Lemma lem389809 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term233 n P n'.
Proof. exact (conj (@lem389692 n P n' h1 h2 h3) (@lem389699 P n' h2)). Qed.
Lemma lem389811 (_8198 : nat) (P : nat -> Prop) (_8199 : nat) : term232 _8198 P _8199.
Proof. exact (EQ_MP (@lem389807 _8198 P _8199) (@lem389786 _8199 P _8198)). Qed.
Lemma lem389812 (P : nat -> Prop) (n : nat -> nat) (n' : nat) : term234 P n n'.
Proof. exact (@lem389811 n' P (term210 n n')). Qed.
Lemma lem389815 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term235 P n n'.
Proof. exact (@lem389812 P n n' (@lem389809 n P n' h1 h2 h3)). Qed.
Lemma lem389816 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term236 P n n'.
Proof. exact (fun h0 : term237 P n n' => @lem389815 n P n' h1 h2 h3). Qed.
Lemma lem389818 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389819 (P : nat -> Prop) (n : nat -> nat) (n' : nat) : (term236 P n n') = (term235 P n n').
Proof. exact (@lem389818 (term235 P n n')). Qed.
Lemma lem389820 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term235 P n n'.
Proof. exact (EQ_MP (@lem389819 P n n') (@lem389816 n P n' h1 h2 h3)). Qed.
Lemma lem389823 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem389825 (P : nat -> Prop) (_8189 : nat) : (term41 P _8189) = (term179 P _8189).
Proof. exact (@lem389823 (term30 P _8189)). Qed.
Lemma lem389828 (_8189 : nat) (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term179 P _8189.
Proof. exact (EQ_MP (@lem389825 P _8189) (@lem389494 _8189 P n' h1)). Qed.
Lemma lem389829 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term105 P n') : term238 P n n'.
Proof. exact (@lem389828 (n n') P n' h1). Qed.
Lemma lem389832 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : False.
Proof. exact (@lem389829 n P n' h2 (@lem389820 n P n' h1 h2 h3)). Qed.
Lemma lem389833 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : term180.
Proof. exact (fun h0 : ~ False => @lem389832 n P n' h1 h2 h3). Qed.
Lemma lem389835 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem389836 : term180 = False.
Proof. exact (@lem389835 False). Qed.
Lemma lem389837 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : False.
Proof. exact (EQ_MP (@lem389836) (@lem389833 n P n' h1 h2 h3)). Qed.
Lemma lem389838 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : (term169 n) = False.
Proof. exact (prop_ext (fun h4 : term169 n => @lem389837 n P n' h1 h2 h3) (fun h4 : False => @lem389435 n h1)). Qed.
Lemma lem389839 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term105 P n') (h3 : term126 P n') : False.
Proof. exact (EQ_MP (@lem389838 n P n' h1 h2 h3) (@lem389435 n h1)). Qed.
Lemma lem389840 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term126 P n') : False.
Proof. exact (or_elim (@lem389373 P n' h2) (fun h0 : term82 n' P => @lem389558 n' P h0) (fun h0 : term105 P n' => @lem389839 n P n' h1 h0 h2)). Qed.
Lemma lem389841 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term126 P n') : (term126 P n') = False.
Proof. exact (prop_ext (fun h3 : term126 P n' => @lem389840 n P n' h1 h2) (fun h3 : False => @lem389372 P n' h2)). Qed.
Lemma lem389842 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term126 P n') : False.
Proof. exact (EQ_MP (@lem389841 n P n' h1 h2) (@lem389372 P n' h2)). Qed.
Lemma lem389843 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term126 P n') : (term169 n) = False.
Proof. exact (prop_ext (fun h3 : term169 n => @lem389842 n P n' h1 h2) (fun h3 : False => @lem389326 n h1)). Qed.
Lemma lem389844 (n : nat -> nat) (P : nat -> Prop) (n' : nat) (h1 : term169 n) (h2 : term126 P n') : False.
Proof. exact (EQ_MP (@lem389843 n P n' h1 h2) (@lem389326 n h1)). Qed.
Lemma lem389845 (n : nat -> nat) (P : nat -> Prop) (h1 : term169 n) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem389152 P h2) (fun n' : nat => fun h0 : term128 P n' => @lem389844 n P n' h1 h0)). Qed.
Lemma lem389846 (P : nat -> Prop) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem389286 h1) (fun n : nat -> nat => fun h0 : term171 n => @lem389845 n P h0 h2)). Qed.
Lemma lem389847 (P : nat -> Prop) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem389846 P h0 h1). Qed.
Lemma lem389848 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem389849 (P : nat -> Prop) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem389848) (@lem389847 P h1)). Qed.
Lemma lem389850 (P : nat -> Prop) (h1 : term3 P) : term13.
Proof. exact (fun h0 : term27 => @lem389849 P h1). Qed.
Lemma lem389851 (P : nat -> Prop) : term15 P.
Proof. exact (fun h0 : term3 P => @lem389850 P h0). Qed.
Lemma lem389856 : term19.
Proof. exact (fun P : nat -> Prop => @lem389851 P). Qed.
Lemma lem389857 : term18.
Proof. exact (EQ_MP (@lem389000) (@lem389856)). Qed.
Lemma lem389858 (P : nat -> Prop) : term239 P.
Proof. exact (@lem389857 P). Qed.
Lemma lem389859 (P : nat -> Prop) : (term239 P) = (term4 P).
Proof. exact (eq_refl (term239 P)). Qed.
Lemma lem389860 (P : nat -> Prop) : term4 P.
Proof. exact (EQ_MP (@lem389859 P) (@lem389858 P)). Qed.
Lemma lem389862 (P : nat -> Prop) : term4 P.
Proof. exact (@lem388807 P (@lem389860 P)). Qed.
Lemma lem389863 (P : nat -> Prop) (h1 : term3 P) : term12.
Proof. exact (@lem389862 P (@lem388792 P h1)). Qed.
Lemma lem389864 (P : nat -> Prop) (h1 : term3 P) : term8.
Proof. exact (@lem389863 P h1 (@lem75570)). Qed.
Lemma lem389865 (P : nat -> Prop) (h1 : term3 P) : False.
Proof. exact (@lem389864 P h1 (@lem76132)). Qed.
Lemma lem389866 (P : nat -> Prop) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem389865 P h1) (fun h2 : False => @lem388792 P h1)). Qed.
Lemma lem389867 (P : nat -> Prop) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem389866 P h1) (@lem388792 P h1)). Qed.
Lemma lem389868 (P : nat -> Prop) : term2 P.
Proof. exact (fun h0 : term3 P => @lem389867 P h0). Qed.
Lemma lem389869 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem388791 P) (@lem389868 P)). Qed.
Lemma lem389880 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem389881 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term240 n P.
Proof. exact (h1). Qed.
Lemma lem389882 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term241 n P.
Proof. exact (h1). Qed.
Lemma lem389884 (P : nat -> Prop) : term242 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem389885 (n : nat) (P : nat -> Prop) : term243 n P.
Proof. exact (@lem389884 (term244 n P)). Qed.
Lemma lem389886 (n : nat) (P : nat -> Prop) : (term245 n P) = (term246 n P).
Proof. exact (eq_refl (term245 n P)). Qed.
Lemma lem389887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389888 (n : nat) (P : nat -> Prop) : (term247 n P) = (term248 n P).
Proof. exact (MK_COMB (@lem389887) (@lem389886 n P)). Qed.
Lemma lem389889 (n : nat) (P : nat -> Prop) (m : nat) : (term249 n P m) = (term250 n P m).
Proof. exact (eq_refl (term249 n P m)). Qed.
Lemma lem389890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389891 (n : nat) (P : nat -> Prop) (m : nat) : (term251 n P m) = (term252 n P m).
Proof. exact (MK_COMB (@lem389890) (@lem389889 n P m)). Qed.
Lemma lem389892 (n : nat) (P : nat -> Prop) (m : nat) : (term253 n P m) = (term254 n P m).
Proof. exact (eq_refl (term253 n P m)). Qed.
Lemma lem389893 (n : nat) (P : nat -> Prop) (m : nat) : (term255 n P m) = (term256 n P m).
Proof. exact (MK_COMB (@lem389891 n P m) (@lem389892 n P m)). Qed.
Lemma lem389894 (n : nat) (P : nat -> Prop) : (term257 n P) = (term258 n P).
Proof. exact (fun_ext (fun m : nat => @lem389893 n P m)). Qed.
Lemma lem389895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389896 (n : nat) (P : nat -> Prop) : (term259 n P) = (term260 n P).
Proof. exact (MK_COMB (@lem389895) (@lem389894 n P)). Qed.
Lemma lem389897 (n : nat) (P : nat -> Prop) : (term261 n P) = (term262 n P).
Proof. exact (MK_COMB (@lem389888 n P) (@lem389896 n P)). Qed.
Lemma lem389898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389899 (n : nat) (P : nat -> Prop) : (term263 n P) = (term264 n P).
Proof. exact (MK_COMB (@lem389898) (@lem389897 n P)). Qed.
Lemma lem389900 (n : nat) (P : nat -> Prop) (m : nat) : (term249 n P m) = (term250 n P m).
Proof. exact (eq_refl (term249 n P m)). Qed.
Lemma lem389901 (n : nat) (P : nat -> Prop) : (term265 n P) = (term244 n P).
Proof. exact (fun_ext (fun m : nat => @lem389900 n P m)). Qed.
Lemma lem389902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389903 (n : nat) (P : nat -> Prop) : (term266 n P) = (term241 n P).
Proof. exact (MK_COMB (@lem389902) (@lem389901 n P)). Qed.
Lemma lem389904 (n : nat) (P : nat -> Prop) : (term243 n P) = (term267 n P).
Proof. exact (MK_COMB (@lem389899 n P) (@lem389903 n P)). Qed.
Lemma lem389905 (n : nat) (P : nat -> Prop) : term267 n P.
Proof. exact (EQ_MP (@lem389904 n P) (@lem389885 n P)). Qed.
Lemma lem389906 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term250 n P m) : term250 n P m.
Proof. exact (h1). Qed.
Lemma lem389908 (P : nat -> Prop) : term242 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem389909 (n : nat) (P : nat -> Prop) : term268 n P.
Proof. exact (@lem389908 (term269 n P)). Qed.
Lemma lem389910 (n : nat) (P : nat -> Prop) : (term270 n P) = (term271 n P).
Proof. exact (eq_refl (term270 n P)). Qed.
Lemma lem389911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem389912 (n : nat) (P : nat -> Prop) : (term272 n P) = (term273 n P).
Proof. exact (MK_COMB (@lem389911) (@lem389910 n P)). Qed.
Lemma lem389913 (n : nat) (P : nat -> Prop) (m : nat) : (term274 n P m) = (term275 n P m).
Proof. exact (eq_refl (term274 n P m)). Qed.
Lemma lem389914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389915 (n : nat) (P : nat -> Prop) (m : nat) : (term276 n P m) = (term277 n P m).
Proof. exact (MK_COMB (@lem389914) (@lem389913 n P m)). Qed.
Lemma lem389916 (n : nat) (P : nat -> Prop) (m : nat) : (term278 n P m) = (term279 n P m).
Proof. exact (eq_refl (term278 n P m)). Qed.
Lemma lem389917 (n : nat) (P : nat -> Prop) (m : nat) : (term280 n P m) = (term281 n P m).
Proof. exact (MK_COMB (@lem389915 n P m) (@lem389916 n P m)). Qed.
Lemma lem389918 (n : nat) (P : nat -> Prop) : (term282 n P) = (term283 n P).
Proof. exact (fun_ext (fun m : nat => @lem389917 n P m)). Qed.
Lemma lem389919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389920 (n : nat) (P : nat -> Prop) : (term284 n P) = (term285 n P).
Proof. exact (MK_COMB (@lem389919) (@lem389918 n P)). Qed.
Lemma lem389921 (n : nat) (P : nat -> Prop) : (term286 n P) = (term287 n P).
Proof. exact (MK_COMB (@lem389912 n P) (@lem389920 n P)). Qed.
Lemma lem389922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem389923 (n : nat) (P : nat -> Prop) : (term288 n P) = (term289 n P).
Proof. exact (MK_COMB (@lem389922) (@lem389921 n P)). Qed.
Lemma lem389924 (n : nat) (P : nat -> Prop) (m : nat) : (term274 n P m) = (term275 n P m).
Proof. exact (eq_refl (term274 n P m)). Qed.
Lemma lem389925 (n : nat) (P : nat -> Prop) : (term290 n P) = (term269 n P).
Proof. exact (fun_ext (fun m : nat => @lem389924 n P m)). Qed.
Lemma lem389926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem389927 (n : nat) (P : nat -> Prop) : (term291 n P) = (term240 n P).
Proof. exact (MK_COMB (@lem389926) (@lem389925 n P)). Qed.
Lemma lem389928 (n : nat) (P : nat -> Prop) : (term268 n P) = (term292 n P).
Proof. exact (MK_COMB (@lem389923 n P) (@lem389927 n P)). Qed.
Lemma lem389929 (n : nat) (P : nat -> Prop) : term292 n P.
Proof. exact (EQ_MP (@lem389928 n P) (@lem389909 n P)). Qed.
Lemma lem389930 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term275 n P m) : term275 n P m.
Proof. exact (h1). Qed.
Lemma lem389932 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem389933 (n : nat) (P : nat -> Prop) : (term246 n P) = (term293 n P).
Proof. exact (@lem389932 (term246 n P)). Qed.
Lemma lem389934 (n : nat) (P : nat -> Prop) : (term293 n P) = (term246 n P).
Proof. exact (SYM (@lem389933 n P)). Qed.
Lemma lem389935 (n : nat) (P : nat -> Prop) (h1 : term294 n P) : term294 n P.
Proof. exact (h1). Qed.
Lemma lem389938 (n : nat) (P : nat -> Prop) (h1 : term295 n P) : term295 n P.
Proof. exact (h1). Qed.
Lemma lem389939 (n : nat) (P : nat -> Prop) : term296 n P.
Proof. exact (fun h0 : term295 n P => @lem389938 n P h0). Qed.
Lemma lem389940 (n : nat) (P : nat -> Prop) (h1 : term296 n P) : term296 n P.
Proof. exact (h1). Qed.
Lemma lem389941 (n : nat) (P : nat -> Prop) (h1 : term295 n P) : term295 n P.
Proof. exact (h1). Qed.
Lemma lem389942 (n : nat) (P : nat -> Prop) (h1 : term295 n P) (h2 : term296 n P) : term295 n P.
Proof. exact (@lem389940 n P h2 (@lem389941 n P h1)). Qed.
Lemma lem389943 (n : nat) (P : nat -> Prop) (h1 : term295 n P) : term297 n P.
Proof. exact (fun h0 : term296 n P => @lem389942 n P h1 h0). Qed.
Lemma lem389944 (n : nat) (P : nat -> Prop) (h1 : term296 n P) : term296 n P.
Proof. exact (h1). Qed.
Lemma lem389945 (n : nat) (P : nat -> Prop) (h1 : term295 n P) (h2 : term296 n P) : term295 n P.
Proof. exact (@lem389943 n P h1 (@lem389944 n P h2)). Qed.
Lemma lem389946 (n : nat) (P : nat -> Prop) (h1 : term296 n P) : term296 n P.
Proof. exact (fun h0 : term295 n P => @lem389945 n P h0 h1). Qed.
Lemma lem389947 (n : nat) (P : nat -> Prop) : term298 n P.
Proof. exact (fun h0 : term296 n P => @lem389946 n P h0). Qed.
Lemma lem389950 (n : nat) (P : nat -> Prop) : term296 n P.
Proof. exact (@lem389947 n P (@lem389939 n P)). Qed.
Lemma lem389980 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem389981 : term299 = term300.
Proof. exact (@lem389980 term301). Qed.
Lemma lem389990 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem389991 : term303 = term304.
Proof. exact (MK_COMB (@lem389990) (@lem389981)). Qed.
Lemma lem389994 (n : nat) (P : nat -> Prop) : (term305 n P) = (term305 n P).
Proof. exact (eq_refl (term305 n P)). Qed.
Lemma lem389995 (n : nat) (P : nat -> Prop) : (term306 n P) = (term307 n P).
Proof. exact (MK_COMB (@lem389994 n P) (@lem389991)). Qed.
Lemma lem389998 (n : nat) (P : nat -> Prop) : (term308 n P) = (term308 n P).
Proof. exact (eq_refl (term308 n P)). Qed.
Lemma lem389999 (n : nat) (P : nat -> Prop) : (term309 n P) = (term310 n P).
Proof. exact (MK_COMB (@lem389998 n P) (@lem389995 n P)). Qed.
Lemma lem390002 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem390003 (n : nat) (P : nat -> Prop) : (term295 n P) = (term312 n P).
Proof. exact (MK_COMB (@lem390002 P) (@lem389999 n P)). Qed.
Lemma lem390006 (P : nat -> Prop) : (term313 P) = (term314 P).
Proof. exact (fun_ext (fun n : nat => @lem390003 n P)). Qed.
Lemma lem390007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390008 (P : nat -> Prop) : (term315 P) = (term316 P).
Proof. exact (MK_COMB (@lem390007) (@lem390006 P)). Qed.
Lemma lem390013 : term317 = term318.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem390008 P)). Qed.
Lemma lem390014 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem390023 : term319 = term320.
Proof. exact (MK_COMB (@lem390014) (@lem390013)). Qed.
Lemma lem390028 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = ((term321 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term321 m n) = (Peano.lt m n))). Qed.
Lemma lem390029 (m : nat) : (term322 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem390028 m n)). Qed.
Lemma lem390030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390031 (m : nat) : (term323 m) = (term323 m).
Proof. exact (MK_COMB (@lem390030) (@lem390029 m)). Qed.
Lemma lem390032 : term324 = term324.
Proof. exact (fun_ext (fun m : nat => @lem390031 m)). Qed.
Lemma lem390033 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390034 : term301 = term301.
Proof. exact (MK_COMB (@lem390033) (@lem390032)). Qed.
Lemma lem390035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem390036 : term300 = term300.
Proof. exact (MK_COMB (@lem390035) (@lem390034)). Qed.
Lemma lem390037 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem390038 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem390037 n)). Qed.
Lemma lem390039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390040 : term327 = term327.
Proof. exact (MK_COMB (@lem390039) (@lem390038)). Qed.
Lemma lem390041 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem390042 : term302 = term302.
Proof. exact (MK_COMB (@lem390041) (@lem390040)). Qed.
Lemma lem390043 : term304 = term304.
Proof. exact (MK_COMB (@lem390042) (@lem390036)). Qed.
Lemma lem390052 (n : nat) (P : nat -> Prop) : (term305 n P) = (term305 n P).
Proof. exact (eq_refl (term305 n P)). Qed.
Lemma lem390053 (n : nat) (P : nat -> Prop) : (term307 n P) = (term307 n P).
Proof. exact (MK_COMB (@lem390052 n P) (@lem390043)). Qed.
Lemma lem390058 (n : nat) (P : nat -> Prop) (m : nat) : (term275 n P m) = (term275 n P m).
Proof. exact (eq_refl (term275 n P m)). Qed.
Lemma lem390059 (n : nat) (P : nat -> Prop) : (term269 n P) = (term269 n P).
Proof. exact (fun_ext (fun m : nat => @lem390058 n P m)). Qed.
Lemma lem390060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390061 (n : nat) (P : nat -> Prop) : (term240 n P) = (term240 n P).
Proof. exact (MK_COMB (@lem390060) (@lem390059 n P)). Qed.
Lemma lem390062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem390063 (n : nat) (P : nat -> Prop) : (term308 n P) = (term308 n P).
Proof. exact (MK_COMB (@lem390062) (@lem390061 n P)). Qed.
Lemma lem390064 (n : nat) (P : nat -> Prop) : (term310 n P) = (term310 n P).
Proof. exact (MK_COMB (@lem390063 n P) (@lem390053 n P)). Qed.
Lemma lem390067 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem390068 (n : nat) (P : nat -> Prop) : (term312 n P) = (term312 n P).
Proof. exact (MK_COMB (@lem390067 P) (@lem390064 n P)). Qed.
Lemma lem390069 (P : nat -> Prop) : (term314 P) = (term314 P).
Proof. exact (fun_ext (fun n : nat => @lem390068 n P)). Qed.
Lemma lem390070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390071 (P : nat -> Prop) : (term316 P) = (term316 P).
Proof. exact (MK_COMB (@lem390070) (@lem390069 P)). Qed.
Lemma lem390072 : term318 = term318.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem390071 P)). Qed.
Lemma lem390073 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem390074 : term320 = term320.
Proof. exact (MK_COMB (@lem390073) (@lem390072)). Qed.
Lemma lem390125 : term319 = term320.
Proof. exact (TRANS (@lem390023) (@lem390074)). Qed.
Lemma lem390126 : term320 = term319.
Proof. exact (SYM (@lem390125)). Qed.
Lemma lem390129 (n : nat) (P : nat -> Prop) (h1 : term294 n P) : term294 n P.
Proof. exact (h1). Qed.
Lemma lem390137 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem390211 (n : nat) (P : nat -> Prop) : (term294 n P) = (term328 n P).
Proof. exact (@lem17362 (term325 n) (term188 P)). Qed.
Lemma lem390518 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem390557 (n : nat) (P : nat -> Prop) (h1 : term294 n P) : term328 n P.
Proof. exact (EQ_MP (@lem390211 n P) (@lem390129 n P h1)). Qed.
Lemma lem390632 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem390712 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem390736 (n : nat) (P : nat -> Prop) (h1 : term294 n P) : term67 P.
Proof. exact (proj2 (@lem390557 n P h1)). Qed.
Lemma lem390738 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem390739 (P : nat -> Prop) (h1 : term188 P) : term329 P.
Proof. exact (fun h0 : term67 P => @lem390738 P h1). Qed.
Lemma lem390741 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem390742 (P : nat -> Prop) : (term329 P) = (term188 P).
Proof. exact (@lem390741 (term188 P)). Qed.
Lemma lem390743 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (EQ_MP (@lem390742 P) (@lem390739 P h1)). Qed.
Lemma lem390746 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem390748 (P : nat -> Prop) : (term67 P) = (term330 P).
Proof. exact (@lem390746 (term188 P)). Qed.
Lemma lem390751 (n : nat) (P : nat -> Prop) (h1 : term294 n P) : term330 P.
Proof. exact (EQ_MP (@lem390748 P) (@lem390736 n P h1)). Qed.
Lemma lem390754 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (@lem390751 n P h1 (@lem390743 P h2)). Qed.
Lemma lem390755 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : term180.
Proof. exact (fun h0 : ~ False => @lem390754 n P h1 h2). Qed.
Lemma lem390757 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem390758 : term180 = False.
Proof. exact (@lem390757 False). Qed.
Lemma lem390759 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390758) (@lem390755 n P h1 h2)). Qed.
Lemma lem390760 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : (term188 P) = False.
Proof. exact (prop_ext (fun h3 : term188 P => @lem390759 n P h1 h2) (fun h3 : False => @lem390712 P h2)). Qed.
Lemma lem390761 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390760 n P h1 h2) (@lem390712 P h2)). Qed.
Lemma lem390762 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : (term188 P) = False.
Proof. exact (prop_ext (fun h3 : term188 P => @lem390761 n P h1 h2) (fun h3 : False => @lem390632 P h2)). Qed.
Lemma lem390763 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390762 n P h1 h2) (@lem390632 P h2)). Qed.
Lemma lem390764 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : (term188 P) = False.
Proof. exact (prop_ext (fun h3 : term188 P => @lem390763 n P h1 h2) (fun h3 : False => @lem390632 P h2)). Qed.
Lemma lem390765 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390764 n P h1 h2) (@lem390632 P h2)). Qed.
Lemma lem390766 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : (term188 P) = False.
Proof. exact (prop_ext (fun h3 : term188 P => @lem390765 n P h1 h2) (fun h3 : False => @lem390518 P h2)). Qed.
Lemma lem390767 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390766 n P h1 h2) (@lem390518 P h2)). Qed.
Lemma lem390768 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : (term188 P) = False.
Proof. exact (prop_ext (fun h3 : term188 P => @lem390767 n P h1 h2) (fun h3 : False => @lem390137 P h2)). Qed.
Lemma lem390769 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : False.
Proof. exact (EQ_MP (@lem390768 n P h1 h2) (@lem390137 P h2)). Qed.
Lemma lem390770 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : term299.
Proof. exact (fun h0 : term301 => @lem390769 n P h1 h2). Qed.
Lemma lem390771 : term299 = term300.
Proof. exact (@lem69 term301). Qed.
Lemma lem390772 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : term300.
Proof. exact (EQ_MP (@lem390771) (@lem390770 n P h1 h2)). Qed.
Lemma lem390773 (n : nat) (P : nat -> Prop) (h1 : term294 n P) (h2 : term188 P) : term304.
Proof. exact (fun h0 : term327 => @lem390772 n P h1 h2). Qed.
Lemma lem390774 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term307 n P.
Proof. exact (fun h0 : term294 n P => @lem390773 n P h0 h1). Qed.
Lemma lem390775 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term310 n P.
Proof. exact (fun h0 : term240 n P => @lem390774 n P h1). Qed.
Lemma lem390776 (n : nat) (P : nat -> Prop) : term312 n P.
Proof. exact (fun h0 : term188 P => @lem390775 n P h0). Qed.
Lemma lem390781 (P : nat -> Prop) : term316 P.
Proof. exact (fun n : nat => @lem390776 n P). Qed.
Lemma lem390786 : term320.
Proof. exact (fun P : nat -> Prop => @lem390781 P). Qed.
Lemma lem390787 : term319.
Proof. exact (EQ_MP (@lem390126) (@lem390786)). Qed.
Lemma lem390788 (P : nat -> Prop) : term331 P.
Proof. exact (@lem390787 P). Qed.
Lemma lem390789 (P : nat -> Prop) : (term331 P) = (term315 P).
Proof. exact (eq_refl (term331 P)). Qed.
Lemma lem390790 (P : nat -> Prop) : term315 P.
Proof. exact (EQ_MP (@lem390789 P) (@lem390788 P)). Qed.
Lemma lem390791 (P : nat -> Prop) (n : nat) : term332 P n.
Proof. exact (@lem390790 P n). Qed.
Lemma lem390792 (n : nat) (P : nat -> Prop) : (term332 P n) = (term295 n P).
Proof. exact (eq_refl (term332 P n)). Qed.
Lemma lem390793 (n : nat) (P : nat -> Prop) : term295 n P.
Proof. exact (EQ_MP (@lem390792 n P) (@lem390791 P n)). Qed.
Lemma lem390795 (n : nat) (P : nat -> Prop) : term295 n P.
Proof. exact (@lem389950 n P (@lem390793 n P)). Qed.
Lemma lem390796 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term309 n P.
Proof. exact (@lem390795 n P (@lem389880 P h1)). Qed.
Lemma lem390797 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term306 n P.
Proof. exact (@lem390796 n P h2 (@lem389881 n P h1)). Qed.
Lemma lem390798 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term294 n P) (h3 : term188 P) : term303.
Proof. exact (@lem390797 n P h1 h3 (@lem389935 n P h2)). Qed.
Lemma lem390799 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term294 n P) (h3 : term188 P) : term299.
Proof. exact (@lem390798 n P h1 h2 h3 (@lem91530)). Qed.
Lemma lem390800 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term294 n P) (h3 : term188 P) : False.
Proof. exact (@lem390799 n P h1 h2 h3 (@lem91415)). Qed.
Lemma lem390801 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term294 n P) (h3 : term188 P) : (term294 n P) = False.
Proof. exact (prop_ext (fun h4 : term294 n P => @lem390800 n P h1 h2 h3) (fun h4 : False => @lem389935 n P h2)). Qed.
Lemma lem390802 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term294 n P) (h3 : term188 P) : False.
Proof. exact (EQ_MP (@lem390801 n P h1 h2 h3) (@lem389935 n P h2)). Qed.
Lemma lem390803 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term293 n P.
Proof. exact (fun h0 : term294 n P => @lem390802 n P h1 h0 h2). Qed.
Lemma lem390804 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term246 n P.
Proof. exact (EQ_MP (@lem389934 n P) (@lem390803 n P h1 h2)). Qed.
Lemma lem390806 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem390807 (n : nat) (P : nat -> Prop) (m : nat) : (term254 n P m) = (term333 n P m).
Proof. exact (@lem390806 (term254 n P m)). Qed.
Lemma lem390808 (n : nat) (P : nat -> Prop) (m : nat) : (term333 n P m) = (term254 n P m).
Proof. exact (SYM (@lem390807 n P m)). Qed.
Lemma lem390809 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term334 n P m.
Proof. exact (h1). Qed.
Lemma lem390812 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term335 n P m) : term335 n P m.
Proof. exact (h1). Qed.
Lemma lem390813 (n : nat) (P : nat -> Prop) (m : nat) : term336 n P m.
Proof. exact (fun h0 : term335 n P m => @lem390812 n P m h0). Qed.
Lemma lem390814 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term336 n P m) : term336 n P m.
Proof. exact (h1). Qed.
Lemma lem390815 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term335 n P m) : term335 n P m.
Proof. exact (h1). Qed.
Lemma lem390816 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term335 n P m) (h2 : term336 n P m) : term335 n P m.
Proof. exact (@lem390814 n P m h2 (@lem390815 n P m h1)). Qed.
Lemma lem390817 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term335 n P m) : term337 n P m.
Proof. exact (fun h0 : term336 n P m => @lem390816 n P m h1 h0). Qed.
Lemma lem390818 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term336 n P m) : term336 n P m.
Proof. exact (h1). Qed.
Lemma lem390819 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term335 n P m) (h2 : term336 n P m) : term335 n P m.
Proof. exact (@lem390817 n P m h1 (@lem390818 n P m h2)). Qed.
Lemma lem390820 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term336 n P m) : term336 n P m.
Proof. exact (fun h0 : term335 n P m => @lem390819 n P m h0 h1). Qed.
Lemma lem390821 (n : nat) (P : nat -> Prop) (m : nat) : term338 n P m.
Proof. exact (fun h0 : term336 n P m => @lem390820 n P m h0). Qed.
Lemma lem390824 (n : nat) (P : nat -> Prop) (m : nat) : term336 n P m.
Proof. exact (@lem390821 n P m (@lem390813 n P m)). Qed.
Lemma lem390862 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem390863 : term299 = term300.
Proof. exact (@lem390862 term301). Qed.
Lemma lem390872 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem390873 : term303 = term304.
Proof. exact (MK_COMB (@lem390872) (@lem390863)). Qed.
Lemma lem390876 (n : nat) (P : nat -> Prop) (m : nat) : (term339 n P m) = (term339 n P m).
Proof. exact (eq_refl (term339 n P m)). Qed.
Lemma lem390877 (n : nat) (P : nat -> Prop) (m : nat) : (term340 n P m) = (term341 n P m).
Proof. exact (MK_COMB (@lem390876 n P m) (@lem390873)). Qed.
Lemma lem390880 (n : nat) (P : nat -> Prop) (m : nat) : (term252 n P m) = (term252 n P m).
Proof. exact (eq_refl (term252 n P m)). Qed.
Lemma lem390881 (n : nat) (P : nat -> Prop) (m : nat) : (term342 n P m) = (term343 n P m).
Proof. exact (MK_COMB (@lem390880 n P m) (@lem390877 n P m)). Qed.
Lemma lem390884 (n : nat) (P : nat -> Prop) : (term308 n P) = (term308 n P).
Proof. exact (eq_refl (term308 n P)). Qed.
Lemma lem390885 (n : nat) (P : nat -> Prop) (m : nat) : (term344 n P m) = (term345 n P m).
Proof. exact (MK_COMB (@lem390884 n P) (@lem390881 n P m)). Qed.
Lemma lem390888 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem390889 (n : nat) (P : nat -> Prop) (m : nat) : (term335 n P m) = (term346 n P m).
Proof. exact (MK_COMB (@lem390888 P) (@lem390885 n P m)). Qed.
Lemma lem390892 (P : nat -> Prop) (m : nat) : (term347 P m) = (term348 P m).
Proof. exact (fun_ext (fun n : nat => @lem390889 n P m)). Qed.
Lemma lem390893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390894 (P : nat -> Prop) (m : nat) : (term349 P m) = (term350 P m).
Proof. exact (MK_COMB (@lem390893) (@lem390892 P m)). Qed.
Lemma lem390899 (m : nat) : (term351 m) = (term352 m).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem390894 P m)). Qed.
Lemma lem390900 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem390901 (m : nat) : (term353 m) = (term354 m).
Proof. exact (MK_COMB (@lem390900) (@lem390899 m)). Qed.
Lemma lem390906 : term355 = term356.
Proof. exact (fun_ext (fun m : nat => @lem390901 m)). Qed.
Lemma lem390907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390916 : term357 = term358.
Proof. exact (MK_COMB (@lem390907) (@lem390906)). Qed.
Lemma lem390921 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = ((term321 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term321 m n) = (Peano.lt m n))). Qed.
Lemma lem390922 (m : nat) : (term322 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem390921 m n)). Qed.
Lemma lem390923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390924 (m : nat) : (term323 m) = (term323 m).
Proof. exact (MK_COMB (@lem390923) (@lem390922 m)). Qed.
Lemma lem390925 : term324 = term324.
Proof. exact (fun_ext (fun m : nat => @lem390924 m)). Qed.
Lemma lem390926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390927 : term301 = term301.
Proof. exact (MK_COMB (@lem390926) (@lem390925)). Qed.
Lemma lem390928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem390929 : term300 = term300.
Proof. exact (MK_COMB (@lem390928) (@lem390927)). Qed.
Lemma lem390930 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem390931 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem390930 n)). Qed.
Lemma lem390932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390933 : term327 = term327.
Proof. exact (MK_COMB (@lem390932) (@lem390931)). Qed.
Lemma lem390934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem390935 : term302 = term302.
Proof. exact (MK_COMB (@lem390934) (@lem390933)). Qed.
Lemma lem390936 : term304 = term304.
Proof. exact (MK_COMB (@lem390935) (@lem390929)). Qed.
Lemma lem390945 (n : nat) (P : nat -> Prop) (m : nat) : (term339 n P m) = (term339 n P m).
Proof. exact (eq_refl (term339 n P m)). Qed.
Lemma lem390946 (n : nat) (P : nat -> Prop) (m : nat) : (term341 n P m) = (term341 n P m).
Proof. exact (MK_COMB (@lem390945 n P m) (@lem390936)). Qed.
Lemma lem390953 (n : nat) (P : nat -> Prop) (m : nat) : (term252 n P m) = (term252 n P m).
Proof. exact (eq_refl (term252 n P m)). Qed.
Lemma lem390954 (n : nat) (P : nat -> Prop) (m : nat) : (term343 n P m) = (term343 n P m).
Proof. exact (MK_COMB (@lem390953 n P m) (@lem390946 n P m)). Qed.
Lemma lem390959 (n : nat) (P : nat -> Prop) (m : nat) : (term275 n P m) = (term275 n P m).
Proof. exact (eq_refl (term275 n P m)). Qed.
Lemma lem390960 (n : nat) (P : nat -> Prop) : (term269 n P) = (term269 n P).
Proof. exact (fun_ext (fun m : nat => @lem390959 n P m)). Qed.
Lemma lem390961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390962 (n : nat) (P : nat -> Prop) : (term240 n P) = (term240 n P).
Proof. exact (MK_COMB (@lem390961) (@lem390960 n P)). Qed.
Lemma lem390963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem390964 (n : nat) (P : nat -> Prop) : (term308 n P) = (term308 n P).
Proof. exact (MK_COMB (@lem390963) (@lem390962 n P)). Qed.
Lemma lem390965 (n : nat) (P : nat -> Prop) (m : nat) : (term345 n P m) = (term345 n P m).
Proof. exact (MK_COMB (@lem390964 n P) (@lem390954 n P m)). Qed.
Lemma lem390968 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem390969 (n : nat) (P : nat -> Prop) (m : nat) : (term346 n P m) = (term346 n P m).
Proof. exact (MK_COMB (@lem390968 P) (@lem390965 n P m)). Qed.
Lemma lem390970 (P : nat -> Prop) (m : nat) : (term348 P m) = (term348 P m).
Proof. exact (fun_ext (fun n : nat => @lem390969 n P m)). Qed.
Lemma lem390971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390972 (P : nat -> Prop) (m : nat) : (term350 P m) = (term350 P m).
Proof. exact (MK_COMB (@lem390971) (@lem390970 P m)). Qed.
Lemma lem390973 (m : nat) : (term352 m) = (term352 m).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem390972 P m)). Qed.
Lemma lem390974 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem390975 (m : nat) : (term354 m) = (term354 m).
Proof. exact (MK_COMB (@lem390974) (@lem390973 m)). Qed.
Lemma lem390976 : term356 = term356.
Proof. exact (fun_ext (fun m : nat => @lem390975 m)). Qed.
Lemma lem390977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem390978 : term358 = term358.
Proof. exact (MK_COMB (@lem390977) (@lem390976)). Qed.
Lemma lem391039 : term357 = term358.
Proof. exact (TRANS (@lem390916) (@lem390978)). Qed.
Lemma lem391040 : term358 = term357.
Proof. exact (SYM (@lem391039)). Qed.
Lemma lem391042 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term240 n P.
Proof. exact (h1). Qed.
Lemma lem391043 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term250 n P m) : term250 n P m.
Proof. exact (h1). Qed.
Lemma lem391044 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term334 n P m.
Proof. exact (h1). Qed.
Lemma lem391046 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem391059 (n : nat) (P : nat -> Prop) (m : nat) : (term275 n P m) = (term359 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term30 P m)). Qed.
Lemma lem391060 (n : nat) (P : nat -> Prop) : (term269 n P) = (term360 n P).
Proof. exact (fun_ext (fun m : nat => @lem391059 n P m)). Qed.
Lemma lem391061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391114 (n : nat) (P : nat -> Prop) : (term240 n P) = (term361 n P).
Proof. exact (MK_COMB (@lem391061) (@lem391060 n P)). Qed.
Lemma lem391115 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term361 n P.
Proof. exact (EQ_MP (@lem391114 n P) (@lem391042 n P h1)). Qed.
Lemma lem391126 (n : nat) (P : nat -> Prop) (m : nat) : (term250 n P m) = (term362 n P m).
Proof. exact (@lem17265 (term363 m n) (P m)). Qed.
Lemma lem391138 (n : nat) (P : nat -> Prop) (m : nat) : (term334 n P m) = (term364 n P m).
Proof. exact (@lem17362 (term321 m n) (term30 P m)). Qed.
Lemma lem391167 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = (term365 m n).
Proof. exact (@lem17784 (term321 m n) (Peano.lt m n)). Qed.
Lemma lem391168 (m : nat) : (term322 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem391167 m n)). Qed.
Lemma lem391169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391170 (m : nat) : (term323 m) = (term367 m).
Proof. exact (MK_COMB (@lem391169) (@lem391168 m)). Qed.
Lemma lem391171 : term324 = term368.
Proof. exact (fun_ext (fun m : nat => @lem391170 m)). Qed.
Lemma lem391172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391173 : term301 = term369.
Proof. exact (MK_COMB (@lem391172) (@lem391171)). Qed.
Lemma lem391179 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem391180 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem391179 nat P Q). Qed.
Lemma lem391181 (m : nat) : (term374 m) = (term375 m).
Proof. exact (@lem391180 (term376 m) (term377 m)). Qed.
Lemma lem391182 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem391183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem391184 (m : nat) (n : nat) : (term380 m n) = (term381 m n).
Proof. exact (MK_COMB (@lem391183) (@lem391182 m n)). Qed.
Lemma lem391185 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem391186 (m : nat) (n : nat) : (term384 m n) = (term365 m n).
Proof. exact (MK_COMB (@lem391184 m n) (@lem391185 m n)). Qed.
Lemma lem391187 (m : nat) : (term385 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem391186 m n)). Qed.
Lemma lem391188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391189 (m : nat) : (term374 m) = (term367 m).
Proof. exact (MK_COMB (@lem391188) (@lem391187 m)). Qed.
Lemma lem391190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem391191 (m : nat) : (term386 m) = (term387 m).
Proof. exact (MK_COMB (@lem391190) (@lem391189 m)). Qed.
Lemma lem391192 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem391193 (m : nat) : (term388 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem391192 m n)). Qed.
Lemma lem391194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391195 (m : nat) : (term389 m) = (term390 m).
Proof. exact (MK_COMB (@lem391194) (@lem391193 m)). Qed.
Lemma lem391196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem391197 (m : nat) : (term391 m) = (term392 m).
Proof. exact (MK_COMB (@lem391196) (@lem391195 m)). Qed.
Lemma lem391198 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem391199 (m : nat) : (term393 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem391198 m n)). Qed.
Lemma lem391200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391201 (m : nat) : (term394 m) = (term395 m).
Proof. exact (MK_COMB (@lem391200) (@lem391199 m)). Qed.
Lemma lem391202 (m : nat) : (term375 m) = (term396 m).
Proof. exact (MK_COMB (@lem391197 m) (@lem391201 m)). Qed.
Lemma lem391203 (m : nat) : ((term374 m) = (term375 m)) = ((term367 m) = (term396 m)).
Proof. exact (MK_COMB (@lem391191 m) (@lem391202 m)). Qed.
Lemma lem391204 (m : nat) : (term367 m) = (term396 m).
Proof. exact (EQ_MP (@lem391203 m) (@lem391181 m)). Qed.
Lemma lem391301 : term368 = term397.
Proof. exact (fun_ext (fun m : nat => @lem391204 m)). Qed.
Lemma lem391302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391303 : term369 = term398.
Proof. exact (MK_COMB (@lem391302) (@lem391301)). Qed.
Lemma lem391305 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem391306 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem391305 nat P Q). Qed.
Lemma lem391307 : term399 = term400.
Proof. exact (@lem391306 term401 term402). Qed.
Lemma lem391308 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem391309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem391310 (m : nat) : (term404 m) = (term392 m).
Proof. exact (MK_COMB (@lem391309) (@lem391308 m)). Qed.
Lemma lem391311 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem391312 (m : nat) : (term406 m) = (term396 m).
Proof. exact (MK_COMB (@lem391310 m) (@lem391311 m)). Qed.
Lemma lem391313 : term407 = term397.
Proof. exact (fun_ext (fun m : nat => @lem391312 m)). Qed.
Lemma lem391314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391315 : term399 = term398.
Proof. exact (MK_COMB (@lem391314) (@lem391313)). Qed.
Lemma lem391316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem391317 : term408 = term409.
Proof. exact (MK_COMB (@lem391316) (@lem391315)). Qed.
Lemma lem391318 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem391319 : term410 = term401.
Proof. exact (fun_ext (fun m : nat => @lem391318 m)). Qed.
Lemma lem391320 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391321 : term411 = term412.
Proof. exact (MK_COMB (@lem391320) (@lem391319)). Qed.
Lemma lem391322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem391323 : term413 = term414.
Proof. exact (MK_COMB (@lem391322) (@lem391321)). Qed.
Lemma lem391324 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem391325 : term415 = term402.
Proof. exact (fun_ext (fun m : nat => @lem391324 m)). Qed.
Lemma lem391326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391327 : term416 = term417.
Proof. exact (MK_COMB (@lem391326) (@lem391325)). Qed.
Lemma lem391328 : term400 = term418.
Proof. exact (MK_COMB (@lem391323) (@lem391327)). Qed.
Lemma lem391329 : (term399 = term400) = (term398 = term418).
Proof. exact (MK_COMB (@lem391317) (@lem391328)). Qed.
Lemma lem391330 : term398 = term418.
Proof. exact (EQ_MP (@lem391329) (@lem391307)). Qed.
Lemma lem391437 : term369 = term418.
Proof. exact (TRANS (@lem391303) (@lem391330)). Qed.
Lemma lem391438 : term301 = term418.
Proof. exact (TRANS (@lem391173) (@lem391437)). Qed.
Lemma lem391439 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem391438) (@lem391046 h1)). Qed.
Lemma lem391460 (n : nat) (P : nat -> Prop) (m : nat) : (term359 n P m) = (term359 n P m).
Proof. exact (eq_refl (term359 n P m)). Qed.
Lemma lem391461 (n : nat) (P : nat -> Prop) : (term360 n P) = (term360 n P).
Proof. exact (fun_ext (fun m : nat => @lem391460 n P m)). Qed.
Lemma lem391462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391463 (n : nat) (P : nat -> Prop) : (term361 n P) = (term361 n P).
Proof. exact (MK_COMB (@lem391462) (@lem391461 n P)). Qed.
Lemma lem391464 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term361 n P.
Proof. exact (EQ_MP (@lem391463 n P) (@lem391115 n P h1)). Qed.
Lemma lem391480 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term250 n P m) : term362 n P m.
Proof. exact (EQ_MP (@lem391126 n P m) (@lem391043 n P m h1)). Qed.
Lemma lem391500 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term364 n P m.
Proof. exact (EQ_MP (@lem391138 n P m) (@lem391044 n P m h1)). Qed.
Lemma lem391532 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem391533 (m : nat) : (term377 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem391532 m n)). Qed.
Lemma lem391534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391535 (m : nat) : (term395 m) = (term395 m).
Proof. exact (MK_COMB (@lem391534) (@lem391533 m)). Qed.
Lemma lem391536 : term402 = term402.
Proof. exact (fun_ext (fun m : nat => @lem391535 m)). Qed.
Lemma lem391537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391538 : term417 = term417.
Proof. exact (MK_COMB (@lem391537) (@lem391536)). Qed.
Lemma lem391557 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem391558 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem391557 m n)). Qed.
Lemma lem391559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391560 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem391559) (@lem391558 m)). Qed.
Lemma lem391561 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem391560 m)). Qed.
Lemma lem391562 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391563 : term412 = term412.
Proof. exact (MK_COMB (@lem391562) (@lem391561)). Qed.
Lemma lem391564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem391565 : term414 = term414.
Proof. exact (MK_COMB (@lem391564) (@lem391563)). Qed.
Lemma lem391566 : term418 = term418.
Proof. exact (MK_COMB (@lem391565) (@lem391538)). Qed.
Lemma lem391567 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem391566) (@lem391439 h1)). Qed.
Lemma lem391568 (h1 : term301) : term417.
Proof. exact (proj2 (@lem391567 h1)). Qed.
Lemma lem391585 (n : nat) (P : nat -> Prop) (m : nat) : (term359 n P m) = (term359 n P m).
Proof. exact (eq_refl (term359 n P m)). Qed.
Lemma lem391586 (n : nat) (P : nat -> Prop) : (term360 n P) = (term360 n P).
Proof. exact (fun_ext (fun m : nat => @lem391585 n P m)). Qed.
Lemma lem391587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391589 (n : nat) (P : nat -> Prop) : (term361 n P) = (term361 n P).
Proof. exact (MK_COMB (@lem391587) (@lem391586 n P)). Qed.
Lemma lem391590 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term361 n P.
Proof. exact (EQ_MP (@lem391589 n P) (@lem391464 n P h1)). Qed.
Lemma lem391621 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem391622 (m : nat) : (term377 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem391621 m n)). Qed.
Lemma lem391623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391624 (m : nat) : (term395 m) = (term395 m).
Proof. exact (MK_COMB (@lem391623) (@lem391622 m)). Qed.
Lemma lem391625 : term402 = term402.
Proof. exact (fun_ext (fun m : nat => @lem391624 m)). Qed.
Lemma lem391626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391628 : term417 = term417.
Proof. exact (MK_COMB (@lem391626) (@lem391625)). Qed.
Lemma lem391629 (h1 : term301) : term417.
Proof. exact (EQ_MP (@lem391628) (@lem391568 h1)). Qed.
Lemma lem391653 (n : nat) (P : nat -> Prop) (m : nat) : (term359 n P m) = (term359 n P m).
Proof. exact (eq_refl (term359 n P m)). Qed.
Lemma lem391654 (n : nat) (P : nat -> Prop) : (term360 n P) = (term360 n P).
Proof. exact (fun_ext (fun m : nat => @lem391653 n P m)). Qed.
Lemma lem391655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391657 (n : nat) (P : nat -> Prop) : (term361 n P) = (term361 n P).
Proof. exact (MK_COMB (@lem391655) (@lem391654 n P)). Qed.
Lemma lem391658 (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term361 n P.
Proof. exact (EQ_MP (@lem391657 n P) (@lem391464 n P h1)). Qed.
Lemma lem391689 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem391690 (m : nat) : (term377 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem391689 m n)). Qed.
Lemma lem391691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391692 (m : nat) : (term395 m) = (term395 m).
Proof. exact (MK_COMB (@lem391691) (@lem391690 m)). Qed.
Lemma lem391693 : term402 = term402.
Proof. exact (fun_ext (fun m : nat => @lem391692 m)). Qed.
Lemma lem391694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem391696 : term417 = term417.
Proof. exact (MK_COMB (@lem391694) (@lem391693)). Qed.
Lemma lem391697 (h1 : term301) : term417.
Proof. exact (EQ_MP (@lem391696) (@lem391568 h1)). Qed.
Lemma lem391710 (_8212 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term419 n P _8212.
Proof. exact (@lem391590 n P h1 _8212). Qed.
Lemma lem391711 (n : nat) (P : nat -> Prop) (_8212 : nat) : (term419 n P _8212) = (term359 n P _8212).
Proof. exact (eq_refl (term419 n P _8212)). Qed.
Lemma lem391722 (_8216 : nat) (h1 : term301) : term405 _8216.
Proof. exact (@lem391629 h1 _8216). Qed.
Lemma lem391723 (_8216 : nat) : (term405 _8216) = (term395 _8216).
Proof. exact (eq_refl (term405 _8216)). Qed.
Lemma lem391724 (_8216 : nat) (h1 : term301) : term395 _8216.
Proof. exact (EQ_MP (@lem391723 _8216) (@lem391722 _8216 h1)). Qed.
Lemma lem391725 (_8216 : nat) (_8217 : nat) (h1 : term301) : term382 _8216 _8217.
Proof. exact (@lem391724 _8216 h1 _8217). Qed.
Lemma lem391726 (_8216 : nat) (_8217 : nat) : (term382 _8216 _8217) = (term383 _8216 _8217).
Proof. exact (eq_refl (term382 _8216 _8217)). Qed.
Lemma lem391728 (_8218 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term419 n P _8218.
Proof. exact (@lem391658 n P h1 _8218). Qed.
Lemma lem391729 (n : nat) (P : nat -> Prop) (_8218 : nat) : (term419 n P _8218) = (term359 n P _8218).
Proof. exact (eq_refl (term419 n P _8218)). Qed.
Lemma lem391740 (_8222 : nat) (h1 : term301) : term405 _8222.
Proof. exact (@lem391697 h1 _8222). Qed.
Lemma lem391741 (_8222 : nat) : (term405 _8222) = (term395 _8222).
Proof. exact (eq_refl (term405 _8222)). Qed.
Lemma lem391742 (_8222 : nat) (h1 : term301) : term395 _8222.
Proof. exact (EQ_MP (@lem391741 _8222) (@lem391740 _8222 h1)). Qed.
Lemma lem391743 (_8222 : nat) (_8223 : nat) (h1 : term301) : term382 _8222 _8223.
Proof. exact (@lem391742 _8222 h1 _8223). Qed.
Lemma lem391744 (_8222 : nat) (_8223 : nat) : (term382 _8222 _8223) = (term383 _8222 _8223).
Proof. exact (eq_refl (term382 _8222 _8223)). Qed.
Lemma lem391753 (_8212 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term359 n P _8212.
Proof. exact (EQ_MP (@lem391711 n P _8212) (@lem391710 _8212 n P h1)). Qed.
Lemma lem391767 (_8216 : nat) (_8217 : nat) (h1 : term301) : term383 _8216 _8217.
Proof. exact (EQ_MP (@lem391726 _8216 _8217) (@lem391725 _8216 _8217 h1)). Qed.
Lemma lem391771 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term41 P m.
Proof. exact (proj2 (@lem391500 n P m h1)). Qed.
Lemma lem391781 (_8218 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term359 n P _8218.
Proof. exact (EQ_MP (@lem391729 n P _8218) (@lem391728 _8218 n P h1)). Qed.
Lemma lem391795 (_8222 : nat) (_8223 : nat) (h1 : term301) : term383 _8222 _8223.
Proof. exact (EQ_MP (@lem391744 _8222 _8223) (@lem391743 _8222 _8223 h1)). Qed.
Lemma lem391799 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term41 P m.
Proof. exact (proj2 (@lem391500 n P m h1)). Qed.
Lemma lem391803 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term321 m n.
Proof. exact (proj1 (@lem391500 n P m h1)). Qed.
Lemma lem391804 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term420 m n.
Proof. exact (fun h0 : term421 m n => @lem391803 n P m h1). Qed.
Lemma lem391806 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391807 (m : nat) (n : nat) : (term420 m n) = (term321 m n).
Proof. exact (@lem391806 (term321 m n)). Qed.
Lemma lem391808 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term321 m n.
Proof. exact (EQ_MP (@lem391807 m n) (@lem391804 n P m h1)). Qed.
Lemma lem391814 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem391815 (_8216 : nat) (_8217 : nat) : (term383 _8216 _8217) = (term422 _8216 _8217).
Proof. exact (@lem391814 (Peano.lt _8216 _8217) (term421 _8216 _8217)). Qed.
Lemma lem391821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem391822 (_8216 : nat) (_8217 : nat) : (term423 _8216 _8217) = (term424 _8216 _8217).
Proof. exact (MK_COMB (@lem391821) (@lem391815 _8216 _8217)). Qed.
Lemma lem391828 (_8216 : nat) (_8217 : nat) : (term422 _8216 _8217) = (term422 _8216 _8217).
Proof. exact (eq_refl (term422 _8216 _8217)). Qed.
Lemma lem391829 (_8216 : nat) (_8217 : nat) : ((term383 _8216 _8217) = (term422 _8216 _8217)) = ((term422 _8216 _8217) = (term422 _8216 _8217)).
Proof. exact (MK_COMB (@lem391822 _8216 _8217) (@lem391828 _8216 _8217)). Qed.
Lemma lem391831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem391832 (x : Prop) : (x = x) = True.
Proof. exact (@lem391831 Prop x). Qed.
Lemma lem391833 (_8216 : nat) (_8217 : nat) : ((term422 _8216 _8217) = (term422 _8216 _8217)) = True.
Proof. exact (@lem391832 (term422 _8216 _8217)). Qed.
Lemma lem391834 (_8216 : nat) (_8217 : nat) : ((term383 _8216 _8217) = (term422 _8216 _8217)) = True.
Proof. exact (TRANS (@lem391829 _8216 _8217) (@lem391833 _8216 _8217)). Qed.
Lemma lem391835 (_8216 : nat) (_8217 : nat) : True = ((term383 _8216 _8217) = (term422 _8216 _8217)).
Proof. exact (SYM (@lem391834 _8216 _8217)). Qed.
Lemma lem391836 (_8216 : nat) (_8217 : nat) : (term383 _8216 _8217) = (term422 _8216 _8217).
Proof. exact (EQ_MP (@lem391835 _8216 _8217) (@lem0)). Qed.
Lemma lem391837 (_8216 : nat) (_8217 : nat) (h1 : term301) : term422 _8216 _8217.
Proof. exact (EQ_MP (@lem391836 _8216 _8217) (@lem391767 _8216 _8217 h1)). Qed.
Lemma lem391839 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem391840 (_8216 : nat) (_8217 : nat) : (term422 _8216 _8217) = (term425 _8216 _8217).
Proof. exact (@lem391839 (term421 _8216 _8217) (Peano.lt _8216 _8217)). Qed.
Lemma lem391842 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem391843 (_8216 : nat) (_8217 : nat) : (term426 _8216 _8217) = (term321 _8216 _8217).
Proof. exact (@lem391842 (term321 _8216 _8217)). Qed.
Lemma lem391844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem391845 (_8216 : nat) (_8217 : nat) : (term427 _8216 _8217) = (term428 _8216 _8217).
Proof. exact (MK_COMB (@lem391844) (@lem391843 _8216 _8217)). Qed.
Lemma lem391846 (_8216 : nat) (_8217 : nat) : (Peano.lt _8216 _8217) = (Peano.lt _8216 _8217).
Proof. exact (eq_refl (Peano.lt _8216 _8217)). Qed.
Lemma lem391847 (_8216 : nat) (_8217 : nat) : (term425 _8216 _8217) = (term429 _8216 _8217).
Proof. exact (MK_COMB (@lem391845 _8216 _8217) (@lem391846 _8216 _8217)). Qed.
Lemma lem391848 (_8216 : nat) (_8217 : nat) : (term422 _8216 _8217) = (term429 _8216 _8217).
Proof. exact (TRANS (@lem391840 _8216 _8217) (@lem391847 _8216 _8217)). Qed.
Lemma lem391851 (_8216 : nat) (_8217 : nat) (h1 : term301) : term429 _8216 _8217.
Proof. exact (EQ_MP (@lem391848 _8216 _8217) (@lem391837 _8216 _8217 h1)). Qed.
Lemma lem391852 (m : nat) (n : nat) (h1 : term301) : term429 m n.
Proof. exact (@lem391851 m n h1). Qed.
Lemma lem391855 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : Peano.lt m n.
Proof. exact (@lem391852 m n h1 (@lem391808 n P m h2)). Qed.
Lemma lem391856 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : term430 m n.
Proof. exact (fun h0 : term431 m n => @lem391855 n P m h1 h2). Qed.
Lemma lem391858 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391859 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (@lem391858 (Peano.lt m n)). Qed.
Lemma lem391860 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : Peano.lt m n.
Proof. exact (EQ_MP (@lem391859 m n) (@lem391856 n P m h1 h2)). Qed.
Lemma lem391866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem391867 (P : nat -> Prop) (_8212 : nat) (n : nat) : (term359 n P _8212) = (term432 P _8212 n).
Proof. exact (@lem391866 (term30 P _8212) (term431 _8212 n)). Qed.
Lemma lem391873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem391874 (P : nat -> Prop) (_8212 : nat) (n : nat) : (term433 n P _8212) = (term434 P _8212 n).
Proof. exact (MK_COMB (@lem391873) (@lem391867 P _8212 n)). Qed.
Lemma lem391880 (P : nat -> Prop) (_8212 : nat) (n : nat) : (term432 P _8212 n) = (term432 P _8212 n).
Proof. exact (eq_refl (term432 P _8212 n)). Qed.
Lemma lem391881 (P : nat -> Prop) (_8212 : nat) (n : nat) : ((term359 n P _8212) = (term432 P _8212 n)) = ((term432 P _8212 n) = (term432 P _8212 n)).
Proof. exact (MK_COMB (@lem391874 P _8212 n) (@lem391880 P _8212 n)). Qed.
Lemma lem391883 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem391884 (x : Prop) : (x = x) = True.
Proof. exact (@lem391883 Prop x). Qed.
Lemma lem391885 (P : nat -> Prop) (_8212 : nat) (n : nat) : ((term432 P _8212 n) = (term432 P _8212 n)) = True.
Proof. exact (@lem391884 (term432 P _8212 n)). Qed.
Lemma lem391886 (P : nat -> Prop) (_8212 : nat) (n : nat) : ((term359 n P _8212) = (term432 P _8212 n)) = True.
Proof. exact (TRANS (@lem391881 P _8212 n) (@lem391885 P _8212 n)). Qed.
Lemma lem391887 (P : nat -> Prop) (_8212 : nat) (n : nat) : True = ((term359 n P _8212) = (term432 P _8212 n)).
Proof. exact (SYM (@lem391886 P _8212 n)). Qed.
Lemma lem391888 (P : nat -> Prop) (_8212 : nat) (n : nat) : (term359 n P _8212) = (term432 P _8212 n).
Proof. exact (EQ_MP (@lem391887 P _8212 n) (@lem0)). Qed.
Lemma lem391889 (_8212 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term432 P _8212 n.
Proof. exact (EQ_MP (@lem391888 P _8212 n) (@lem391753 _8212 n P h1)). Qed.
Lemma lem391891 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem391892 (n : nat) (P : nat -> Prop) (_8212 : nat) : (term432 P _8212 n) = (term435 n P _8212).
Proof. exact (@lem391891 (term431 _8212 n) (term30 P _8212)). Qed.
Lemma lem391894 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem391895 (_8212 : nat) (n : nat) : (term436 _8212 n) = (Peano.lt _8212 n).
Proof. exact (@lem391894 (Peano.lt _8212 n)). Qed.
Lemma lem391896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem391897 (_8212 : nat) (n : nat) : (term437 _8212 n) = (term438 _8212 n).
Proof. exact (MK_COMB (@lem391896) (@lem391895 _8212 n)). Qed.
Lemma lem391898 (P : nat -> Prop) (_8212 : nat) : (term30 P _8212) = (term30 P _8212).
Proof. exact (eq_refl (term30 P _8212)). Qed.
Lemma lem391899 (n : nat) (P : nat -> Prop) (_8212 : nat) : (term435 n P _8212) = (term275 n P _8212).
Proof. exact (MK_COMB (@lem391897 _8212 n) (@lem391898 P _8212)). Qed.
Lemma lem391900 (n : nat) (P : nat -> Prop) (_8212 : nat) : (term432 P _8212 n) = (term275 n P _8212).
Proof. exact (TRANS (@lem391892 n P _8212) (@lem391899 n P _8212)). Qed.
Lemma lem391903 (_8212 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term275 n P _8212.
Proof. exact (EQ_MP (@lem391900 n P _8212) (@lem391889 _8212 n P h1)). Qed.
Lemma lem391904 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term275 n P m.
Proof. exact (@lem391903 m n P h1). Qed.
Lemma lem391907 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term30 P m.
Proof. exact (@lem391904 m n P h2 (@lem391860 n P m h1 h3)). Qed.
Lemma lem391908 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term176 P m.
Proof. exact (fun h0 : term41 P m => @lem391907 n P m h1 h2 h3). Qed.
Lemma lem391910 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391911 (P : nat -> Prop) (m : nat) : (term176 P m) = (term30 P m).
Proof. exact (@lem391910 (term30 P m)). Qed.
Lemma lem391912 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term30 P m.
Proof. exact (EQ_MP (@lem391911 P m) (@lem391908 n P m h1 h2 h3)). Qed.
Lemma lem391915 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem391917 (P : nat -> Prop) (m : nat) : (term41 P m) = (term179 P m).
Proof. exact (@lem391915 (term30 P m)). Qed.
Lemma lem391920 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term179 P m.
Proof. exact (EQ_MP (@lem391917 P m) (@lem391771 n P m h1)). Qed.
Lemma lem391923 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : False.
Proof. exact (@lem391920 n P m h3 (@lem391912 n P m h1 h2 h3)). Qed.
Lemma lem391924 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term180.
Proof. exact (fun h0 : ~ False => @lem391923 n P m h1 h2 h3). Qed.
Lemma lem391926 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391927 : term180 = False.
Proof. exact (@lem391926 False). Qed.
Lemma lem391928 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : False.
Proof. exact (EQ_MP (@lem391927) (@lem391924 n P m h1 h2 h3)). Qed.
Lemma lem391930 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term321 m n.
Proof. exact (proj1 (@lem391500 n P m h1)). Qed.
Lemma lem391931 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term420 m n.
Proof. exact (fun h0 : term421 m n => @lem391930 n P m h1). Qed.
Lemma lem391933 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391934 (m : nat) (n : nat) : (term420 m n) = (term321 m n).
Proof. exact (@lem391933 (term321 m n)). Qed.
Lemma lem391935 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term321 m n.
Proof. exact (EQ_MP (@lem391934 m n) (@lem391931 n P m h1)). Qed.
Lemma lem391941 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem391942 (_8222 : nat) (_8223 : nat) : (term383 _8222 _8223) = (term422 _8222 _8223).
Proof. exact (@lem391941 (Peano.lt _8222 _8223) (term421 _8222 _8223)). Qed.
Lemma lem391948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem391949 (_8222 : nat) (_8223 : nat) : (term423 _8222 _8223) = (term424 _8222 _8223).
Proof. exact (MK_COMB (@lem391948) (@lem391942 _8222 _8223)). Qed.
Lemma lem391955 (_8222 : nat) (_8223 : nat) : (term422 _8222 _8223) = (term422 _8222 _8223).
Proof. exact (eq_refl (term422 _8222 _8223)). Qed.
Lemma lem391956 (_8222 : nat) (_8223 : nat) : ((term383 _8222 _8223) = (term422 _8222 _8223)) = ((term422 _8222 _8223) = (term422 _8222 _8223)).
Proof. exact (MK_COMB (@lem391949 _8222 _8223) (@lem391955 _8222 _8223)). Qed.
Lemma lem391958 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem391959 (x : Prop) : (x = x) = True.
Proof. exact (@lem391958 Prop x). Qed.
Lemma lem391960 (_8222 : nat) (_8223 : nat) : ((term422 _8222 _8223) = (term422 _8222 _8223)) = True.
Proof. exact (@lem391959 (term422 _8222 _8223)). Qed.
Lemma lem391961 (_8222 : nat) (_8223 : nat) : ((term383 _8222 _8223) = (term422 _8222 _8223)) = True.
Proof. exact (TRANS (@lem391956 _8222 _8223) (@lem391960 _8222 _8223)). Qed.
Lemma lem391962 (_8222 : nat) (_8223 : nat) : True = ((term383 _8222 _8223) = (term422 _8222 _8223)).
Proof. exact (SYM (@lem391961 _8222 _8223)). Qed.
Lemma lem391963 (_8222 : nat) (_8223 : nat) : (term383 _8222 _8223) = (term422 _8222 _8223).
Proof. exact (EQ_MP (@lem391962 _8222 _8223) (@lem0)). Qed.
Lemma lem391964 (_8222 : nat) (_8223 : nat) (h1 : term301) : term422 _8222 _8223.
Proof. exact (EQ_MP (@lem391963 _8222 _8223) (@lem391795 _8222 _8223 h1)). Qed.
Lemma lem391966 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem391967 (_8222 : nat) (_8223 : nat) : (term422 _8222 _8223) = (term425 _8222 _8223).
Proof. exact (@lem391966 (term421 _8222 _8223) (Peano.lt _8222 _8223)). Qed.
Lemma lem391969 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem391970 (_8222 : nat) (_8223 : nat) : (term426 _8222 _8223) = (term321 _8222 _8223).
Proof. exact (@lem391969 (term321 _8222 _8223)). Qed.
Lemma lem391971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem391972 (_8222 : nat) (_8223 : nat) : (term427 _8222 _8223) = (term428 _8222 _8223).
Proof. exact (MK_COMB (@lem391971) (@lem391970 _8222 _8223)). Qed.
Lemma lem391973 (_8222 : nat) (_8223 : nat) : (Peano.lt _8222 _8223) = (Peano.lt _8222 _8223).
Proof. exact (eq_refl (Peano.lt _8222 _8223)). Qed.
Lemma lem391974 (_8222 : nat) (_8223 : nat) : (term425 _8222 _8223) = (term429 _8222 _8223).
Proof. exact (MK_COMB (@lem391972 _8222 _8223) (@lem391973 _8222 _8223)). Qed.
Lemma lem391975 (_8222 : nat) (_8223 : nat) : (term422 _8222 _8223) = (term429 _8222 _8223).
Proof. exact (TRANS (@lem391967 _8222 _8223) (@lem391974 _8222 _8223)). Qed.
Lemma lem391978 (_8222 : nat) (_8223 : nat) (h1 : term301) : term429 _8222 _8223.
Proof. exact (EQ_MP (@lem391975 _8222 _8223) (@lem391964 _8222 _8223 h1)). Qed.
Lemma lem391979 (m : nat) (n : nat) (h1 : term301) : term429 m n.
Proof. exact (@lem391978 m n h1). Qed.
Lemma lem391982 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : Peano.lt m n.
Proof. exact (@lem391979 m n h1 (@lem391935 n P m h2)). Qed.
Lemma lem391983 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : term430 m n.
Proof. exact (fun h0 : term431 m n => @lem391982 n P m h1 h2). Qed.
Lemma lem391985 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem391986 (m : nat) (n : nat) : (term430 m n) = (Peano.lt m n).
Proof. exact (@lem391985 (Peano.lt m n)). Qed.
Lemma lem391987 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term334 n P m) : Peano.lt m n.
Proof. exact (EQ_MP (@lem391986 m n) (@lem391983 n P m h1 h2)). Qed.
Lemma lem391993 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem391994 (P : nat -> Prop) (_8218 : nat) (n : nat) : (term359 n P _8218) = (term432 P _8218 n).
Proof. exact (@lem391993 (term30 P _8218) (term431 _8218 n)). Qed.
Lemma lem392000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem392001 (P : nat -> Prop) (_8218 : nat) (n : nat) : (term433 n P _8218) = (term434 P _8218 n).
Proof. exact (MK_COMB (@lem392000) (@lem391994 P _8218 n)). Qed.
Lemma lem392007 (P : nat -> Prop) (_8218 : nat) (n : nat) : (term432 P _8218 n) = (term432 P _8218 n).
Proof. exact (eq_refl (term432 P _8218 n)). Qed.
Lemma lem392008 (P : nat -> Prop) (_8218 : nat) (n : nat) : ((term359 n P _8218) = (term432 P _8218 n)) = ((term432 P _8218 n) = (term432 P _8218 n)).
Proof. exact (MK_COMB (@lem392001 P _8218 n) (@lem392007 P _8218 n)). Qed.
Lemma lem392010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem392011 (x : Prop) : (x = x) = True.
Proof. exact (@lem392010 Prop x). Qed.
Lemma lem392012 (P : nat -> Prop) (_8218 : nat) (n : nat) : ((term432 P _8218 n) = (term432 P _8218 n)) = True.
Proof. exact (@lem392011 (term432 P _8218 n)). Qed.
Lemma lem392013 (P : nat -> Prop) (_8218 : nat) (n : nat) : ((term359 n P _8218) = (term432 P _8218 n)) = True.
Proof. exact (TRANS (@lem392008 P _8218 n) (@lem392012 P _8218 n)). Qed.
Lemma lem392014 (P : nat -> Prop) (_8218 : nat) (n : nat) : True = ((term359 n P _8218) = (term432 P _8218 n)).
Proof. exact (SYM (@lem392013 P _8218 n)). Qed.
Lemma lem392015 (P : nat -> Prop) (_8218 : nat) (n : nat) : (term359 n P _8218) = (term432 P _8218 n).
Proof. exact (EQ_MP (@lem392014 P _8218 n) (@lem0)). Qed.
Lemma lem392016 (_8218 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term432 P _8218 n.
Proof. exact (EQ_MP (@lem392015 P _8218 n) (@lem391781 _8218 n P h1)). Qed.
Lemma lem392018 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem392019 (n : nat) (P : nat -> Prop) (_8218 : nat) : (term432 P _8218 n) = (term435 n P _8218).
Proof. exact (@lem392018 (term431 _8218 n) (term30 P _8218)). Qed.
Lemma lem392021 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem392022 (_8218 : nat) (n : nat) : (term436 _8218 n) = (Peano.lt _8218 n).
Proof. exact (@lem392021 (Peano.lt _8218 n)). Qed.
Lemma lem392023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem392024 (_8218 : nat) (n : nat) : (term437 _8218 n) = (term438 _8218 n).
Proof. exact (MK_COMB (@lem392023) (@lem392022 _8218 n)). Qed.
Lemma lem392025 (P : nat -> Prop) (_8218 : nat) : (term30 P _8218) = (term30 P _8218).
Proof. exact (eq_refl (term30 P _8218)). Qed.
Lemma lem392026 (n : nat) (P : nat -> Prop) (_8218 : nat) : (term435 n P _8218) = (term275 n P _8218).
Proof. exact (MK_COMB (@lem392024 _8218 n) (@lem392025 P _8218)). Qed.
Lemma lem392027 (n : nat) (P : nat -> Prop) (_8218 : nat) : (term432 P _8218 n) = (term275 n P _8218).
Proof. exact (TRANS (@lem392019 n P _8218) (@lem392026 n P _8218)). Qed.
Lemma lem392030 (_8218 : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term275 n P _8218.
Proof. exact (EQ_MP (@lem392027 n P _8218) (@lem392016 _8218 n P h1)). Qed.
Lemma lem392031 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term275 n P m.
Proof. exact (@lem392030 m n P h1). Qed.
Lemma lem392034 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term30 P m.
Proof. exact (@lem392031 m n P h2 (@lem391987 n P m h1 h3)). Qed.
Lemma lem392035 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term176 P m.
Proof. exact (fun h0 : term41 P m => @lem392034 n P m h1 h2 h3). Qed.
Lemma lem392037 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392038 (P : nat -> Prop) (m : nat) : (term176 P m) = (term30 P m).
Proof. exact (@lem392037 (term30 P m)). Qed.
Lemma lem392039 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term30 P m.
Proof. exact (EQ_MP (@lem392038 P m) (@lem392035 n P m h1 h2 h3)). Qed.
Lemma lem392042 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem392044 (P : nat -> Prop) (m : nat) : (term41 P m) = (term179 P m).
Proof. exact (@lem392042 (term30 P m)). Qed.
Lemma lem392047 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term334 n P m) : term179 P m.
Proof. exact (EQ_MP (@lem392044 P m) (@lem391799 n P m h1)). Qed.
Lemma lem392050 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : False.
Proof. exact (@lem392047 n P m h3 (@lem392039 n P m h1 h2 h3)). Qed.
Lemma lem392051 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : term180.
Proof. exact (fun h0 : ~ False => @lem392050 n P m h1 h2 h3). Qed.
Lemma lem392053 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392054 : term180 = False.
Proof. exact (@lem392053 False). Qed.
Lemma lem392055 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) : False.
Proof. exact (EQ_MP (@lem392054) (@lem392051 n P m h1 h2 h3)). Qed.
Lemma lem392056 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term240 n P) (h3 : term334 n P m) (h4 : term250 n P m) : False.
Proof. exact (or_elim (@lem391480 n P m h4) (fun h0 : term439 m n => @lem391928 n P m h1 h2 h3) (fun h0 : P m => @lem392055 n P m h1 h2 h3)). Qed.
Lemma lem392057 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term250 n P m) : term299.
Proof. exact (fun h0 : term301 => @lem392056 n P m h0 h1 h2 h3). Qed.
Lemma lem392058 : term299 = term300.
Proof. exact (@lem69 term301). Qed.
Lemma lem392059 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term250 n P m) : term300.
Proof. exact (EQ_MP (@lem392058) (@lem392057 n P m h1 h2 h3)). Qed.
Lemma lem392060 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term250 n P m) : term304.
Proof. exact (fun h0 : term327 => @lem392059 n P m h1 h2 h3). Qed.
Lemma lem392061 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term250 n P m) : term341 n P m.
Proof. exact (fun h0 : term334 n P m => @lem392060 n P m h1 h0 h2). Qed.
Lemma lem392062 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) : term343 n P m.
Proof. exact (fun h0 : term250 n P m => @lem392061 n P m h1 h0). Qed.
Lemma lem392063 (n : nat) (P : nat -> Prop) (m : nat) : term345 n P m.
Proof. exact (fun h0 : term240 n P => @lem392062 m n P h0). Qed.
Lemma lem392064 (n : nat) (P : nat -> Prop) (m : nat) : term346 n P m.
Proof. exact (fun h0 : term188 P => @lem392063 n P m). Qed.
Lemma lem392069 (P : nat -> Prop) (m : nat) : term350 P m.
Proof. exact (fun n : nat => @lem392064 n P m). Qed.
Lemma lem392074 (m : nat) : term354 m.
Proof. exact (fun P : nat -> Prop => @lem392069 P m). Qed.
Lemma lem392079 : term358.
Proof. exact (fun m : nat => @lem392074 m). Qed.
Lemma lem392080 : term357.
Proof. exact (EQ_MP (@lem391040) (@lem392079)). Qed.
Lemma lem392081 (m : nat) : term440 m.
Proof. exact (@lem392080 m). Qed.
Lemma lem392082 (m : nat) : (term440 m) = (term353 m).
Proof. exact (eq_refl (term440 m)). Qed.
Lemma lem392083 (m : nat) : term353 m.
Proof. exact (EQ_MP (@lem392082 m) (@lem392081 m)). Qed.
Lemma lem392084 (m : nat) (P : nat -> Prop) : term441 m P.
Proof. exact (@lem392083 m P). Qed.
Lemma lem392085 (P : nat -> Prop) (m : nat) : (term441 m P) = (term349 P m).
Proof. exact (eq_refl (term441 m P)). Qed.
Lemma lem392086 (P : nat -> Prop) (m : nat) : term349 P m.
Proof. exact (EQ_MP (@lem392085 P m) (@lem392084 m P)). Qed.
Lemma lem392087 (P : nat -> Prop) (m : nat) (n : nat) : term442 P m n.
Proof. exact (@lem392086 P m n). Qed.
Lemma lem392088 (n : nat) (P : nat -> Prop) (m : nat) : (term442 P m n) = (term335 n P m).
Proof. exact (eq_refl (term442 P m n)). Qed.
Lemma lem392089 (n : nat) (P : nat -> Prop) (m : nat) : term335 n P m.
Proof. exact (EQ_MP (@lem392088 n P m) (@lem392087 P m n)). Qed.
Lemma lem392091 (n : nat) (P : nat -> Prop) (m : nat) : term335 n P m.
Proof. exact (@lem390824 n P m (@lem392089 n P m)). Qed.
Lemma lem392092 (n : nat) (m : nat) (P : nat -> Prop) (h1 : term188 P) : term344 n P m.
Proof. exact (@lem392091 n P m (@lem389880 P h1)). Qed.
Lemma lem392093 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term342 n P m.
Proof. exact (@lem392092 n m P h2 (@lem389881 n P h1)). Qed.
Lemma lem392094 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term188 P) (h3 : term250 n P m) : term340 n P m.
Proof. exact (@lem392093 m n P h1 h2 (@lem389906 n P m h3)). Qed.
Lemma lem392095 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term188 P) (h4 : term250 n P m) : term303.
Proof. exact (@lem392094 n P m h1 h3 h4 (@lem390809 n P m h2)). Qed.
Lemma lem392096 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term188 P) (h4 : term250 n P m) : term299.
Proof. exact (@lem392095 n P m h1 h2 h3 h4 (@lem91530)). Qed.
Lemma lem392097 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term188 P) (h4 : term250 n P m) : False.
Proof. exact (@lem392096 n P m h1 h2 h3 h4 (@lem91415)). Qed.
Lemma lem392098 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term188 P) (h4 : term250 n P m) : (term334 n P m) = False.
Proof. exact (prop_ext (fun h5 : term334 n P m => @lem392097 n P m h1 h2 h3 h4) (fun h5 : False => @lem390809 n P m h2)). Qed.
Lemma lem392099 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term334 n P m) (h3 : term188 P) (h4 : term250 n P m) : False.
Proof. exact (EQ_MP (@lem392098 n P m h1 h2 h3 h4) (@lem390809 n P m h2)). Qed.
Lemma lem392100 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term188 P) (h3 : term250 n P m) : term333 n P m.
Proof. exact (fun h0 : term334 n P m => @lem392099 n P m h1 h0 h2 h3). Qed.
Lemma lem392101 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term240 n P) (h2 : term188 P) (h3 : term250 n P m) : term254 n P m.
Proof. exact (EQ_MP (@lem390808 n P m) (@lem392100 n P m h1 h2 h3)). Qed.
Lemma lem392103 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem392104 (n : nat) (P : nat -> Prop) : (term271 n P) = (term443 n P).
Proof. exact (@lem392103 (term271 n P)). Qed.
Lemma lem392105 (n : nat) (P : nat -> Prop) : (term443 n P) = (term271 n P).
Proof. exact (SYM (@lem392104 n P)). Qed.
Lemma lem392106 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term444 n P.
Proof. exact (h1). Qed.
Lemma lem392109 (n : nat) (P : nat -> Prop) (h1 : term445 n P) : term445 n P.
Proof. exact (h1). Qed.
Lemma lem392110 (n : nat) (P : nat -> Prop) : term446 n P.
Proof. exact (fun h0 : term445 n P => @lem392109 n P h0). Qed.
Lemma lem392111 (n : nat) (P : nat -> Prop) (h1 : term446 n P) : term446 n P.
Proof. exact (h1). Qed.
Lemma lem392112 (n : nat) (P : nat -> Prop) (h1 : term445 n P) : term445 n P.
Proof. exact (h1). Qed.
Lemma lem392113 (n : nat) (P : nat -> Prop) (h1 : term445 n P) (h2 : term446 n P) : term445 n P.
Proof. exact (@lem392111 n P h2 (@lem392112 n P h1)). Qed.
Lemma lem392114 (n : nat) (P : nat -> Prop) (h1 : term445 n P) : term447 n P.
Proof. exact (fun h0 : term446 n P => @lem392113 n P h1 h0). Qed.
Lemma lem392115 (n : nat) (P : nat -> Prop) (h1 : term446 n P) : term446 n P.
Proof. exact (h1). Qed.
Lemma lem392116 (n : nat) (P : nat -> Prop) (h1 : term445 n P) (h2 : term446 n P) : term445 n P.
Proof. exact (@lem392114 n P h1 (@lem392115 n P h2)). Qed.
Lemma lem392117 (n : nat) (P : nat -> Prop) (h1 : term446 n P) : term446 n P.
Proof. exact (fun h0 : term445 n P => @lem392116 n P h0 h1). Qed.
Lemma lem392118 (n : nat) (P : nat -> Prop) : term448 n P.
Proof. exact (fun h0 : term446 n P => @lem392117 n P h0). Qed.
Lemma lem392121 (n : nat) (P : nat -> Prop) : term446 n P.
Proof. exact (@lem392118 n P (@lem392110 n P)). Qed.
Lemma lem392151 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem392152 : term299 = term300.
Proof. exact (@lem392151 term301). Qed.
Lemma lem392161 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem392162 : term303 = term304.
Proof. exact (MK_COMB (@lem392161) (@lem392152)). Qed.
Lemma lem392165 (n : nat) (P : nat -> Prop) : (term449 n P) = (term449 n P).
Proof. exact (eq_refl (term449 n P)). Qed.
Lemma lem392166 (n : nat) (P : nat -> Prop) : (term450 n P) = (term451 n P).
Proof. exact (MK_COMB (@lem392165 n P) (@lem392162)). Qed.
Lemma lem392169 (n : nat) (P : nat -> Prop) : (term452 n P) = (term452 n P).
Proof. exact (eq_refl (term452 n P)). Qed.
Lemma lem392170 (n : nat) (P : nat -> Prop) : (term453 n P) = (term454 n P).
Proof. exact (MK_COMB (@lem392169 n P) (@lem392166 n P)). Qed.
Lemma lem392173 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem392174 (n : nat) (P : nat -> Prop) : (term445 n P) = (term455 n P).
Proof. exact (MK_COMB (@lem392173 P) (@lem392170 n P)). Qed.
Lemma lem392177 (P : nat -> Prop) : (term456 P) = (term457 P).
Proof. exact (fun_ext (fun n : nat => @lem392174 n P)). Qed.
Lemma lem392178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392179 (P : nat -> Prop) : (term458 P) = (term459 P).
Proof. exact (MK_COMB (@lem392178) (@lem392177 P)). Qed.
Lemma lem392184 : term460 = term461.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem392179 P)). Qed.
Lemma lem392185 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem392194 : term462 = term463.
Proof. exact (MK_COMB (@lem392185) (@lem392184)). Qed.
Lemma lem392199 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = ((term321 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term321 m n) = (Peano.lt m n))). Qed.
Lemma lem392200 (m : nat) : (term322 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem392199 m n)). Qed.
Lemma lem392201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392202 (m : nat) : (term323 m) = (term323 m).
Proof. exact (MK_COMB (@lem392201) (@lem392200 m)). Qed.
Lemma lem392203 : term324 = term324.
Proof. exact (fun_ext (fun m : nat => @lem392202 m)). Qed.
Lemma lem392204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392205 : term301 = term301.
Proof. exact (MK_COMB (@lem392204) (@lem392203)). Qed.
Lemma lem392206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem392207 : term300 = term300.
Proof. exact (MK_COMB (@lem392206) (@lem392205)). Qed.
Lemma lem392208 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem392209 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem392208 n)). Qed.
Lemma lem392210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392211 : term327 = term327.
Proof. exact (MK_COMB (@lem392210) (@lem392209)). Qed.
Lemma lem392212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem392213 : term302 = term302.
Proof. exact (MK_COMB (@lem392212) (@lem392211)). Qed.
Lemma lem392214 : term304 = term304.
Proof. exact (MK_COMB (@lem392213) (@lem392207)). Qed.
Lemma lem392223 (n : nat) (P : nat -> Prop) : (term449 n P) = (term449 n P).
Proof. exact (eq_refl (term449 n P)). Qed.
Lemma lem392224 (n : nat) (P : nat -> Prop) : (term451 n P) = (term451 n P).
Proof. exact (MK_COMB (@lem392223 n P) (@lem392214)). Qed.
Lemma lem392229 (n : nat) (P : nat -> Prop) (m : nat) : (term250 n P m) = (term250 n P m).
Proof. exact (eq_refl (term250 n P m)). Qed.
Lemma lem392230 (n : nat) (P : nat -> Prop) : (term244 n P) = (term244 n P).
Proof. exact (fun_ext (fun m : nat => @lem392229 n P m)). Qed.
Lemma lem392231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392232 (n : nat) (P : nat -> Prop) : (term241 n P) = (term241 n P).
Proof. exact (MK_COMB (@lem392231) (@lem392230 n P)). Qed.
Lemma lem392233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem392234 (n : nat) (P : nat -> Prop) : (term452 n P) = (term452 n P).
Proof. exact (MK_COMB (@lem392233) (@lem392232 n P)). Qed.
Lemma lem392235 (n : nat) (P : nat -> Prop) : (term454 n P) = (term454 n P).
Proof. exact (MK_COMB (@lem392234 n P) (@lem392224 n P)). Qed.
Lemma lem392238 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem392239 (n : nat) (P : nat -> Prop) : (term455 n P) = (term455 n P).
Proof. exact (MK_COMB (@lem392238 P) (@lem392235 n P)). Qed.
Lemma lem392240 (P : nat -> Prop) : (term457 P) = (term457 P).
Proof. exact (fun_ext (fun n : nat => @lem392239 n P)). Qed.
Lemma lem392241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392242 (P : nat -> Prop) : (term459 P) = (term459 P).
Proof. exact (MK_COMB (@lem392241) (@lem392240 P)). Qed.
Lemma lem392243 : term461 = term461.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem392242 P)). Qed.
Lemma lem392244 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem392245 : term463 = term463.
Proof. exact (MK_COMB (@lem392244) (@lem392243)). Qed.
Lemma lem392296 : term462 = term463.
Proof. exact (TRANS (@lem392194) (@lem392245)). Qed.
Lemma lem392297 : term463 = term462.
Proof. exact (SYM (@lem392296)). Qed.
Lemma lem392299 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term241 n P.
Proof. exact (h1). Qed.
Lemma lem392300 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term444 n P.
Proof. exact (h1). Qed.
Lemma lem392302 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem392315 (n : nat) (P : nat -> Prop) (m : nat) : (term250 n P m) = (term362 n P m).
Proof. exact (@lem17265 (term363 m n) (P m)). Qed.
Lemma lem392316 (n : nat) (P : nat -> Prop) : (term244 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem392315 n P m)). Qed.
Lemma lem392317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392354 (n : nat) (P : nat -> Prop) : (term241 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem392317) (@lem392316 n P)). Qed.
Lemma lem392355 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem392354 n P) (@lem392299 n P h1)). Qed.
Lemma lem392366 (n : nat) (P : nat -> Prop) : (term444 n P) = (term466 n P).
Proof. exact (@lem17362 (term467 n) (term468 P)). Qed.
Lemma lem392395 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = (term365 m n).
Proof. exact (@lem17784 (term321 m n) (Peano.lt m n)). Qed.
Lemma lem392396 (m : nat) : (term322 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem392395 m n)). Qed.
Lemma lem392397 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392398 (m : nat) : (term323 m) = (term367 m).
Proof. exact (MK_COMB (@lem392397) (@lem392396 m)). Qed.
Lemma lem392399 : term324 = term368.
Proof. exact (fun_ext (fun m : nat => @lem392398 m)). Qed.
Lemma lem392400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392401 : term301 = term369.
Proof. exact (MK_COMB (@lem392400) (@lem392399)). Qed.
Lemma lem392407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem392408 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem392407 nat P Q). Qed.
Lemma lem392409 (m : nat) : (term374 m) = (term375 m).
Proof. exact (@lem392408 (term376 m) (term377 m)). Qed.
Lemma lem392410 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem392411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem392412 (m : nat) (n : nat) : (term380 m n) = (term381 m n).
Proof. exact (MK_COMB (@lem392411) (@lem392410 m n)). Qed.
Lemma lem392413 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem392414 (m : nat) (n : nat) : (term384 m n) = (term365 m n).
Proof. exact (MK_COMB (@lem392412 m n) (@lem392413 m n)). Qed.
Lemma lem392415 (m : nat) : (term385 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem392414 m n)). Qed.
Lemma lem392416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392417 (m : nat) : (term374 m) = (term367 m).
Proof. exact (MK_COMB (@lem392416) (@lem392415 m)). Qed.
Lemma lem392418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem392419 (m : nat) : (term386 m) = (term387 m).
Proof. exact (MK_COMB (@lem392418) (@lem392417 m)). Qed.
Lemma lem392420 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem392421 (m : nat) : (term388 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem392420 m n)). Qed.
Lemma lem392422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392423 (m : nat) : (term389 m) = (term390 m).
Proof. exact (MK_COMB (@lem392422) (@lem392421 m)). Qed.
Lemma lem392424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem392425 (m : nat) : (term391 m) = (term392 m).
Proof. exact (MK_COMB (@lem392424) (@lem392423 m)). Qed.
Lemma lem392426 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem392427 (m : nat) : (term393 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem392426 m n)). Qed.
Lemma lem392428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392429 (m : nat) : (term394 m) = (term395 m).
Proof. exact (MK_COMB (@lem392428) (@lem392427 m)). Qed.
Lemma lem392430 (m : nat) : (term375 m) = (term396 m).
Proof. exact (MK_COMB (@lem392425 m) (@lem392429 m)). Qed.
Lemma lem392431 (m : nat) : ((term374 m) = (term375 m)) = ((term367 m) = (term396 m)).
Proof. exact (MK_COMB (@lem392419 m) (@lem392430 m)). Qed.
Lemma lem392432 (m : nat) : (term367 m) = (term396 m).
Proof. exact (EQ_MP (@lem392431 m) (@lem392409 m)). Qed.
Lemma lem392529 : term368 = term397.
Proof. exact (fun_ext (fun m : nat => @lem392432 m)). Qed.
Lemma lem392530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392531 : term369 = term398.
Proof. exact (MK_COMB (@lem392530) (@lem392529)). Qed.
Lemma lem392533 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem392534 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem392533 nat P Q). Qed.
Lemma lem392535 : term399 = term400.
Proof. exact (@lem392534 term401 term402). Qed.
Lemma lem392536 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem392537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem392538 (m : nat) : (term404 m) = (term392 m).
Proof. exact (MK_COMB (@lem392537) (@lem392536 m)). Qed.
Lemma lem392539 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem392540 (m : nat) : (term406 m) = (term396 m).
Proof. exact (MK_COMB (@lem392538 m) (@lem392539 m)). Qed.
Lemma lem392541 : term407 = term397.
Proof. exact (fun_ext (fun m : nat => @lem392540 m)). Qed.
Lemma lem392542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392543 : term399 = term398.
Proof. exact (MK_COMB (@lem392542) (@lem392541)). Qed.
Lemma lem392544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem392545 : term408 = term409.
Proof. exact (MK_COMB (@lem392544) (@lem392543)). Qed.
Lemma lem392546 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem392547 : term410 = term401.
Proof. exact (fun_ext (fun m : nat => @lem392546 m)). Qed.
Lemma lem392548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392549 : term411 = term412.
Proof. exact (MK_COMB (@lem392548) (@lem392547)). Qed.
Lemma lem392550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem392551 : term413 = term414.
Proof. exact (MK_COMB (@lem392550) (@lem392549)). Qed.
Lemma lem392552 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem392553 : term415 = term402.
Proof. exact (fun_ext (fun m : nat => @lem392552 m)). Qed.
Lemma lem392554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392555 : term416 = term417.
Proof. exact (MK_COMB (@lem392554) (@lem392553)). Qed.
Lemma lem392556 : term400 = term418.
Proof. exact (MK_COMB (@lem392551) (@lem392555)). Qed.
Lemma lem392557 : (term399 = term400) = (term398 = term418).
Proof. exact (MK_COMB (@lem392545) (@lem392556)). Qed.
Lemma lem392558 : term398 = term418.
Proof. exact (EQ_MP (@lem392557) (@lem392535)). Qed.
Lemma lem392665 : term369 = term418.
Proof. exact (TRANS (@lem392531) (@lem392558)). Qed.
Lemma lem392666 : term301 = term418.
Proof. exact (TRANS (@lem392401) (@lem392665)). Qed.
Lemma lem392667 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem392666) (@lem392302 h1)). Qed.
Lemma lem392688 (n : nat) (P : nat -> Prop) (m : nat) : (term362 n P m) = (term362 n P m).
Proof. exact (eq_refl (term362 n P m)). Qed.
Lemma lem392689 (n : nat) (P : nat -> Prop) : (term464 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem392688 n P m)). Qed.
Lemma lem392690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392691 (n : nat) (P : nat -> Prop) : (term465 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem392690) (@lem392689 n P)). Qed.
Lemma lem392692 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem392691 n P) (@lem392355 n P h1)). Qed.
Lemma lem392712 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term466 n P.
Proof. exact (EQ_MP (@lem392366 n P) (@lem392300 n P h1)). Qed.
Lemma lem392744 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem392745 (m : nat) : (term377 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem392744 m n)). Qed.
Lemma lem392746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392747 (m : nat) : (term395 m) = (term395 m).
Proof. exact (MK_COMB (@lem392746) (@lem392745 m)). Qed.
Lemma lem392748 : term402 = term402.
Proof. exact (fun_ext (fun m : nat => @lem392747 m)). Qed.
Lemma lem392749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392750 : term417 = term417.
Proof. exact (MK_COMB (@lem392749) (@lem392748)). Qed.
Lemma lem392769 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem392770 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem392769 m n)). Qed.
Lemma lem392771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392772 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem392771) (@lem392770 m)). Qed.
Lemma lem392773 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem392772 m)). Qed.
Lemma lem392774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392775 : term412 = term412.
Proof. exact (MK_COMB (@lem392774) (@lem392773)). Qed.
Lemma lem392776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem392777 : term414 = term414.
Proof. exact (MK_COMB (@lem392776) (@lem392775)). Qed.
Lemma lem392778 : term418 = term418.
Proof. exact (MK_COMB (@lem392777) (@lem392750)). Qed.
Lemma lem392779 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem392778) (@lem392667 h1)). Qed.
Lemma lem392781 (h1 : term301) : term412.
Proof. exact (proj1 (@lem392779 h1)). Qed.
Lemma lem392795 (n : nat) (P : nat -> Prop) (m : nat) : (term362 n P m) = (term362 n P m).
Proof. exact (eq_refl (term362 n P m)). Qed.
Lemma lem392796 (n : nat) (P : nat -> Prop) : (term464 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem392795 n P m)). Qed.
Lemma lem392797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392799 (n : nat) (P : nat -> Prop) : (term465 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem392797) (@lem392796 n P)). Qed.
Lemma lem392800 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem392799 n P) (@lem392692 n P h1)). Qed.
Lemma lem392815 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem392816 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem392815 m n)). Qed.
Lemma lem392817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392818 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem392817) (@lem392816 m)). Qed.
Lemma lem392819 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem392818 m)). Qed.
Lemma lem392820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem392822 : term412 = term412.
Proof. exact (MK_COMB (@lem392820) (@lem392819)). Qed.
Lemma lem392823 (h1 : term301) : term412.
Proof. exact (EQ_MP (@lem392822) (@lem392781 h1)). Qed.
Lemma lem392848 (_8224 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term469 n P _8224.
Proof. exact (@lem392800 n P h1 _8224). Qed.
Lemma lem392849 (n : nat) (P : nat -> Prop) (_8224 : nat) : (term469 n P _8224) = (term362 n P _8224).
Proof. exact (eq_refl (term469 n P _8224)). Qed.
Lemma lem392854 (_8226 : nat) (h1 : term301) : term403 _8226.
Proof. exact (@lem392823 h1 _8226). Qed.
Lemma lem392855 (_8226 : nat) : (term403 _8226) = (term390 _8226).
Proof. exact (eq_refl (term403 _8226)). Qed.
Lemma lem392856 (_8226 : nat) (h1 : term301) : term390 _8226.
Proof. exact (EQ_MP (@lem392855 _8226) (@lem392854 _8226 h1)). Qed.
Lemma lem392857 (_8226 : nat) (_8227 : nat) (h1 : term301) : term378 _8226 _8227.
Proof. exact (@lem392856 _8226 h1 _8227). Qed.
Lemma lem392858 (_8226 : nat) (_8227 : nat) : (term378 _8226 _8227) = (term379 _8226 _8227).
Proof. exact (eq_refl (term378 _8226 _8227)). Qed.
Lemma lem392873 (_8224 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term362 n P _8224.
Proof. exact (EQ_MP (@lem392849 n P _8224) (@lem392848 _8224 n P h1)). Qed.
Lemma lem392881 (_8226 : nat) (_8227 : nat) (h1 : term301) : term379 _8226 _8227.
Proof. exact (EQ_MP (@lem392858 _8226 _8227) (@lem392857 _8226 _8227 h1)). Qed.
Lemma lem392891 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term470 P.
Proof. exact (proj2 (@lem392712 n P h1)). Qed.
Lemma lem392893 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term467 n.
Proof. exact (proj1 (@lem392712 n P h1)). Qed.
Lemma lem392894 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term471 n.
Proof. exact (fun h0 : term472 n => @lem392893 n P h1). Qed.
Lemma lem392896 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392897 (n : nat) : (term471 n) = (term467 n).
Proof. exact (@lem392896 (term467 n)). Qed.
Lemma lem392898 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term467 n.
Proof. exact (EQ_MP (@lem392897 n) (@lem392894 n P h1)). Qed.
Lemma lem392900 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem392901 (_8226 : nat) (_8227 : nat) : (term379 _8226 _8227) = (term473 _8226 _8227).
Proof. exact (@lem392900 (term431 _8226 _8227) (term321 _8226 _8227)). Qed.
Lemma lem392903 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem392904 (_8226 : nat) (_8227 : nat) : (term436 _8226 _8227) = (Peano.lt _8226 _8227).
Proof. exact (@lem392903 (Peano.lt _8226 _8227)). Qed.
Lemma lem392905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem392906 (_8226 : nat) (_8227 : nat) : (term437 _8226 _8227) = (term438 _8226 _8227).
Proof. exact (MK_COMB (@lem392905) (@lem392904 _8226 _8227)). Qed.
Lemma lem392907 (_8226 : nat) (_8227 : nat) : (term321 _8226 _8227) = (term321 _8226 _8227).
Proof. exact (eq_refl (term321 _8226 _8227)). Qed.
Lemma lem392908 (_8226 : nat) (_8227 : nat) : (term473 _8226 _8227) = (term474 _8226 _8227).
Proof. exact (MK_COMB (@lem392906 _8226 _8227) (@lem392907 _8226 _8227)). Qed.
Lemma lem392909 (_8226 : nat) (_8227 : nat) : (term379 _8226 _8227) = (term474 _8226 _8227).
Proof. exact (TRANS (@lem392901 _8226 _8227) (@lem392908 _8226 _8227)). Qed.
Lemma lem392912 (_8226 : nat) (_8227 : nat) (h1 : term301) : term474 _8226 _8227.
Proof. exact (EQ_MP (@lem392909 _8226 _8227) (@lem392881 _8226 _8227 h1)). Qed.
Lemma lem392913 (n : nat) (h1 : term301) : term475 n.
Proof. exact (@lem392912 (NUMERAL 0) n h1). Qed.
Lemma lem392916 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term444 n P) : term476 n.
Proof. exact (@lem392913 n h1 (@lem392898 n P h2)). Qed.
Lemma lem392917 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term444 n P) : term477 n.
Proof. exact (fun h0 : term478 n => @lem392916 n P h1 h2). Qed.
Lemma lem392919 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392920 (n : nat) : (term477 n) = (term476 n).
Proof. exact (@lem392919 (term476 n)). Qed.
Lemma lem392921 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term444 n P) : term476 n.
Proof. exact (EQ_MP (@lem392920 n) (@lem392917 n P h1 h2)). Qed.
Lemma lem392927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem392928 (P : nat -> Prop) (_8224 : nat) (n : nat) : (term362 n P _8224) = (term479 P _8224 n).
Proof. exact (@lem392927 (P _8224) (term439 _8224 n)). Qed.
Lemma lem392934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem392935 (P : nat -> Prop) (_8224 : nat) (n : nat) : (term480 n P _8224) = (term481 P _8224 n).
Proof. exact (MK_COMB (@lem392934) (@lem392928 P _8224 n)). Qed.
Lemma lem392941 (P : nat -> Prop) (_8224 : nat) (n : nat) : (term479 P _8224 n) = (term479 P _8224 n).
Proof. exact (eq_refl (term479 P _8224 n)). Qed.
Lemma lem392942 (P : nat -> Prop) (_8224 : nat) (n : nat) : ((term362 n P _8224) = (term479 P _8224 n)) = ((term479 P _8224 n) = (term479 P _8224 n)).
Proof. exact (MK_COMB (@lem392935 P _8224 n) (@lem392941 P _8224 n)). Qed.
Lemma lem392944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem392945 (x : Prop) : (x = x) = True.
Proof. exact (@lem392944 Prop x). Qed.
Lemma lem392946 (P : nat -> Prop) (_8224 : nat) (n : nat) : ((term479 P _8224 n) = (term479 P _8224 n)) = True.
Proof. exact (@lem392945 (term479 P _8224 n)). Qed.
Lemma lem392947 (P : nat -> Prop) (_8224 : nat) (n : nat) : ((term362 n P _8224) = (term479 P _8224 n)) = True.
Proof. exact (TRANS (@lem392942 P _8224 n) (@lem392946 P _8224 n)). Qed.
Lemma lem392948 (P : nat -> Prop) (_8224 : nat) (n : nat) : True = ((term362 n P _8224) = (term479 P _8224 n)).
Proof. exact (SYM (@lem392947 P _8224 n)). Qed.
Lemma lem392949 (P : nat -> Prop) (_8224 : nat) (n : nat) : (term362 n P _8224) = (term479 P _8224 n).
Proof. exact (EQ_MP (@lem392948 P _8224 n) (@lem0)). Qed.
Lemma lem392950 (_8224 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term479 P _8224 n.
Proof. exact (EQ_MP (@lem392949 P _8224 n) (@lem392873 _8224 n P h1)). Qed.
Lemma lem392952 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem392953 (n : nat) (P : nat -> Prop) (_8224 : nat) : (term479 P _8224 n) = (term482 n P _8224).
Proof. exact (@lem392952 (term439 _8224 n) (P _8224)). Qed.
Lemma lem392955 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem392956 (_8224 : nat) (n : nat) : (term483 _8224 n) = (term363 _8224 n).
Proof. exact (@lem392955 (term363 _8224 n)). Qed.
Lemma lem392957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem392958 (_8224 : nat) (n : nat) : (term484 _8224 n) = (term485 _8224 n).
Proof. exact (MK_COMB (@lem392957) (@lem392956 _8224 n)). Qed.
Lemma lem392959 (P : nat -> Prop) (_8224 : nat) : (P _8224) = (P _8224).
Proof. exact (eq_refl (P _8224)). Qed.
Lemma lem392960 (n : nat) (P : nat -> Prop) (_8224 : nat) : (term482 n P _8224) = (term250 n P _8224).
Proof. exact (MK_COMB (@lem392958 _8224 n) (@lem392959 P _8224)). Qed.
Lemma lem392961 (n : nat) (P : nat -> Prop) (_8224 : nat) : (term479 P _8224 n) = (term250 n P _8224).
Proof. exact (TRANS (@lem392953 n P _8224) (@lem392960 n P _8224)). Qed.
Lemma lem392964 (_8224 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term250 n P _8224.
Proof. exact (EQ_MP (@lem392961 n P _8224) (@lem392950 _8224 n P h1)). Qed.
Lemma lem392965 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term486 n P.
Proof. exact (@lem392964 term487 n P h1). Qed.
Lemma lem392968 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : term468 P.
Proof. exact (@lem392965 n P h2 (@lem392921 n P h1 h3)). Qed.
Lemma lem392969 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : term488 P.
Proof. exact (fun h0 : term470 P => @lem392968 n P h1 h2 h3). Qed.
Lemma lem392971 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392972 (P : nat -> Prop) : (term488 P) = (term468 P).
Proof. exact (@lem392971 (term468 P)). Qed.
Lemma lem392973 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : term468 P.
Proof. exact (EQ_MP (@lem392972 P) (@lem392969 n P h1 h2 h3)). Qed.
Lemma lem392976 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem392978 (P : nat -> Prop) : (term470 P) = (term489 P).
Proof. exact (@lem392976 (term468 P)). Qed.
Lemma lem392981 (n : nat) (P : nat -> Prop) (h1 : term444 n P) : term489 P.
Proof. exact (EQ_MP (@lem392978 P) (@lem392891 n P h1)). Qed.
Lemma lem392984 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : False.
Proof. exact (@lem392981 n P h3 (@lem392973 n P h1 h2 h3)). Qed.
Lemma lem392985 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : term180.
Proof. exact (fun h0 : ~ False => @lem392984 n P h1 h2 h3). Qed.
Lemma lem392987 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem392988 : term180 = False.
Proof. exact (@lem392987 False). Qed.
Lemma lem392989 (n : nat) (P : nat -> Prop) (h1 : term301) (h2 : term241 n P) (h3 : term444 n P) : False.
Proof. exact (EQ_MP (@lem392988) (@lem392985 n P h1 h2 h3)). Qed.
Lemma lem392990 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) : term299.
Proof. exact (fun h0 : term301 => @lem392989 n P h0 h1 h2). Qed.
Lemma lem392991 : term299 = term300.
Proof. exact (@lem69 term301). Qed.
Lemma lem392992 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) : term300.
Proof. exact (EQ_MP (@lem392991) (@lem392990 n P h1 h2)). Qed.
Lemma lem392993 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) : term304.
Proof. exact (fun h0 : term327 => @lem392992 n P h1 h2). Qed.
Lemma lem392994 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term451 n P.
Proof. exact (fun h0 : term444 n P => @lem392993 n P h1 h0). Qed.
Lemma lem392995 (n : nat) (P : nat -> Prop) : term454 n P.
Proof. exact (fun h0 : term241 n P => @lem392994 n P h0). Qed.
Lemma lem392996 (n : nat) (P : nat -> Prop) : term455 n P.
Proof. exact (fun h0 : term188 P => @lem392995 n P). Qed.
Lemma lem393001 (P : nat -> Prop) : term459 P.
Proof. exact (fun n : nat => @lem392996 n P). Qed.
Lemma lem393006 : term463.
Proof. exact (fun P : nat -> Prop => @lem393001 P). Qed.
Lemma lem393007 : term462.
Proof. exact (EQ_MP (@lem392297) (@lem393006)). Qed.
Lemma lem393008 (P : nat -> Prop) : term490 P.
Proof. exact (@lem393007 P). Qed.
Lemma lem393009 (P : nat -> Prop) : (term490 P) = (term458 P).
Proof. exact (eq_refl (term490 P)). Qed.
Lemma lem393010 (P : nat -> Prop) : term458 P.
Proof. exact (EQ_MP (@lem393009 P) (@lem393008 P)). Qed.
Lemma lem393011 (P : nat -> Prop) (n : nat) : term491 P n.
Proof. exact (@lem393010 P n). Qed.
Lemma lem393012 (n : nat) (P : nat -> Prop) : (term491 P n) = (term445 n P).
Proof. exact (eq_refl (term491 P n)). Qed.
Lemma lem393013 (n : nat) (P : nat -> Prop) : term445 n P.
Proof. exact (EQ_MP (@lem393012 n P) (@lem393011 P n)). Qed.
Lemma lem393015 (n : nat) (P : nat -> Prop) : term445 n P.
Proof. exact (@lem392121 n P (@lem393013 n P)). Qed.
Lemma lem393016 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term453 n P.
Proof. exact (@lem393015 n P (@lem389880 P h1)). Qed.
Lemma lem393017 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term450 n P.
Proof. exact (@lem393016 n P h2 (@lem389882 n P h1)). Qed.
Lemma lem393018 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) (h3 : term188 P) : term303.
Proof. exact (@lem393017 n P h1 h3 (@lem392106 n P h2)). Qed.
Lemma lem393019 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) (h3 : term188 P) : term299.
Proof. exact (@lem393018 n P h1 h2 h3 (@lem91530)). Qed.
Lemma lem393020 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) (h3 : term188 P) : False.
Proof. exact (@lem393019 n P h1 h2 h3 (@lem91415)). Qed.
Lemma lem393021 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) (h3 : term188 P) : (term444 n P) = False.
Proof. exact (prop_ext (fun h4 : term444 n P => @lem393020 n P h1 h2 h3) (fun h4 : False => @lem392106 n P h2)). Qed.
Lemma lem393022 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term444 n P) (h3 : term188 P) : False.
Proof. exact (EQ_MP (@lem393021 n P h1 h2 h3) (@lem392106 n P h2)). Qed.
Lemma lem393023 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term443 n P.
Proof. exact (fun h0 : term444 n P => @lem393022 n P h1 h0 h2). Qed.
Lemma lem393024 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term271 n P.
Proof. exact (EQ_MP (@lem392105 n P) (@lem393023 n P h1 h2)). Qed.
Lemma lem393026 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem393027 (n : nat) (P : nat -> Prop) (m : nat) : (term279 n P m) = (term492 n P m).
Proof. exact (@lem393026 (term279 n P m)). Qed.
Lemma lem393028 (n : nat) (P : nat -> Prop) (m : nat) : (term492 n P m) = (term279 n P m).
Proof. exact (SYM (@lem393027 n P m)). Qed.
Lemma lem393029 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term493 n P m.
Proof. exact (h1). Qed.
Lemma lem393032 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term494 n P m) : term494 n P m.
Proof. exact (h1). Qed.
Lemma lem393033 (n : nat) (P : nat -> Prop) (m : nat) : term495 n P m.
Proof. exact (fun h0 : term494 n P m => @lem393032 n P m h0). Qed.
Lemma lem393034 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term495 n P m) : term495 n P m.
Proof. exact (h1). Qed.
Lemma lem393035 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term494 n P m) : term494 n P m.
Proof. exact (h1). Qed.
Lemma lem393036 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term494 n P m) (h2 : term495 n P m) : term494 n P m.
Proof. exact (@lem393034 n P m h2 (@lem393035 n P m h1)). Qed.
Lemma lem393037 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term494 n P m) : term496 n P m.
Proof. exact (fun h0 : term495 n P m => @lem393036 n P m h1 h0). Qed.
Lemma lem393038 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term495 n P m) : term495 n P m.
Proof. exact (h1). Qed.
Lemma lem393039 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term494 n P m) (h2 : term495 n P m) : term494 n P m.
Proof. exact (@lem393037 n P m h1 (@lem393038 n P m h2)). Qed.
Lemma lem393040 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term495 n P m) : term495 n P m.
Proof. exact (fun h0 : term494 n P m => @lem393039 n P m h0 h1). Qed.
Lemma lem393041 (n : nat) (P : nat -> Prop) (m : nat) : term497 n P m.
Proof. exact (fun h0 : term495 n P m => @lem393040 n P m h0). Qed.
Lemma lem393044 (n : nat) (P : nat -> Prop) (m : nat) : term495 n P m.
Proof. exact (@lem393041 n P m (@lem393033 n P m)). Qed.
Lemma lem393082 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem393083 : term299 = term300.
Proof. exact (@lem393082 term301). Qed.
Lemma lem393092 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem393093 : term303 = term304.
Proof. exact (MK_COMB (@lem393092) (@lem393083)). Qed.
Lemma lem393096 (n : nat) (P : nat -> Prop) (m : nat) : (term498 n P m) = (term498 n P m).
Proof. exact (eq_refl (term498 n P m)). Qed.
Lemma lem393097 (n : nat) (P : nat -> Prop) (m : nat) : (term499 n P m) = (term500 n P m).
Proof. exact (MK_COMB (@lem393096 n P m) (@lem393093)). Qed.
Lemma lem393100 (n : nat) (P : nat -> Prop) (m : nat) : (term277 n P m) = (term277 n P m).
Proof. exact (eq_refl (term277 n P m)). Qed.
Lemma lem393101 (n : nat) (P : nat -> Prop) (m : nat) : (term501 n P m) = (term502 n P m).
Proof. exact (MK_COMB (@lem393100 n P m) (@lem393097 n P m)). Qed.
Lemma lem393104 (n : nat) (P : nat -> Prop) : (term452 n P) = (term452 n P).
Proof. exact (eq_refl (term452 n P)). Qed.
Lemma lem393105 (n : nat) (P : nat -> Prop) (m : nat) : (term503 n P m) = (term504 n P m).
Proof. exact (MK_COMB (@lem393104 n P) (@lem393101 n P m)). Qed.
Lemma lem393108 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem393109 (n : nat) (P : nat -> Prop) (m : nat) : (term494 n P m) = (term505 n P m).
Proof. exact (MK_COMB (@lem393108 P) (@lem393105 n P m)). Qed.
Lemma lem393112 (P : nat -> Prop) (m : nat) : (term506 P m) = (term507 P m).
Proof. exact (fun_ext (fun n : nat => @lem393109 n P m)). Qed.
Lemma lem393113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393114 (P : nat -> Prop) (m : nat) : (term508 P m) = (term509 P m).
Proof. exact (MK_COMB (@lem393113) (@lem393112 P m)). Qed.
Lemma lem393119 (m : nat) : (term510 m) = (term511 m).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem393114 P m)). Qed.
Lemma lem393120 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem393121 (m : nat) : (term512 m) = (term513 m).
Proof. exact (MK_COMB (@lem393120) (@lem393119 m)). Qed.
Lemma lem393126 : term514 = term515.
Proof. exact (fun_ext (fun m : nat => @lem393121 m)). Qed.
Lemma lem393127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393136 : term516 = term517.
Proof. exact (MK_COMB (@lem393127) (@lem393126)). Qed.
Lemma lem393141 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = ((term321 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term321 m n) = (Peano.lt m n))). Qed.
Lemma lem393142 (m : nat) : (term322 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem393141 m n)). Qed.
Lemma lem393143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393144 (m : nat) : (term323 m) = (term323 m).
Proof. exact (MK_COMB (@lem393143) (@lem393142 m)). Qed.
Lemma lem393145 : term324 = term324.
Proof. exact (fun_ext (fun m : nat => @lem393144 m)). Qed.
Lemma lem393146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393147 : term301 = term301.
Proof. exact (MK_COMB (@lem393146) (@lem393145)). Qed.
Lemma lem393148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem393149 : term300 = term300.
Proof. exact (MK_COMB (@lem393148) (@lem393147)). Qed.
Lemma lem393150 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem393151 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem393150 n)). Qed.
Lemma lem393152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393153 : term327 = term327.
Proof. exact (MK_COMB (@lem393152) (@lem393151)). Qed.
Lemma lem393154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem393155 : term302 = term302.
Proof. exact (MK_COMB (@lem393154) (@lem393153)). Qed.
Lemma lem393156 : term304 = term304.
Proof. exact (MK_COMB (@lem393155) (@lem393149)). Qed.
Lemma lem393165 (n : nat) (P : nat -> Prop) (m : nat) : (term498 n P m) = (term498 n P m).
Proof. exact (eq_refl (term498 n P m)). Qed.
Lemma lem393166 (n : nat) (P : nat -> Prop) (m : nat) : (term500 n P m) = (term500 n P m).
Proof. exact (MK_COMB (@lem393165 n P m) (@lem393156)). Qed.
Lemma lem393173 (n : nat) (P : nat -> Prop) (m : nat) : (term277 n P m) = (term277 n P m).
Proof. exact (eq_refl (term277 n P m)). Qed.
Lemma lem393174 (n : nat) (P : nat -> Prop) (m : nat) : (term502 n P m) = (term502 n P m).
Proof. exact (MK_COMB (@lem393173 n P m) (@lem393166 n P m)). Qed.
Lemma lem393179 (n : nat) (P : nat -> Prop) (m : nat) : (term250 n P m) = (term250 n P m).
Proof. exact (eq_refl (term250 n P m)). Qed.
Lemma lem393180 (n : nat) (P : nat -> Prop) : (term244 n P) = (term244 n P).
Proof. exact (fun_ext (fun m : nat => @lem393179 n P m)). Qed.
Lemma lem393181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393182 (n : nat) (P : nat -> Prop) : (term241 n P) = (term241 n P).
Proof. exact (MK_COMB (@lem393181) (@lem393180 n P)). Qed.
Lemma lem393183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem393184 (n : nat) (P : nat -> Prop) : (term452 n P) = (term452 n P).
Proof. exact (MK_COMB (@lem393183) (@lem393182 n P)). Qed.
Lemma lem393185 (n : nat) (P : nat -> Prop) (m : nat) : (term504 n P m) = (term504 n P m).
Proof. exact (MK_COMB (@lem393184 n P) (@lem393174 n P m)). Qed.
Lemma lem393188 (P : nat -> Prop) : (term311 P) = (term311 P).
Proof. exact (eq_refl (term311 P)). Qed.
Lemma lem393189 (n : nat) (P : nat -> Prop) (m : nat) : (term505 n P m) = (term505 n P m).
Proof. exact (MK_COMB (@lem393188 P) (@lem393185 n P m)). Qed.
Lemma lem393190 (P : nat -> Prop) (m : nat) : (term507 P m) = (term507 P m).
Proof. exact (fun_ext (fun n : nat => @lem393189 n P m)). Qed.
Lemma lem393191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393192 (P : nat -> Prop) (m : nat) : (term509 P m) = (term509 P m).
Proof. exact (MK_COMB (@lem393191) (@lem393190 P m)). Qed.
Lemma lem393193 (m : nat) : (term511 m) = (term511 m).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem393192 P m)). Qed.
Lemma lem393194 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem393195 (m : nat) : (term513 m) = (term513 m).
Proof. exact (MK_COMB (@lem393194) (@lem393193 m)). Qed.
Lemma lem393196 : term515 = term515.
Proof. exact (fun_ext (fun m : nat => @lem393195 m)). Qed.
Lemma lem393197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393198 : term517 = term517.
Proof. exact (MK_COMB (@lem393197) (@lem393196)). Qed.
Lemma lem393259 : term516 = term517.
Proof. exact (TRANS (@lem393136) (@lem393198)). Qed.
Lemma lem393260 : term517 = term516.
Proof. exact (SYM (@lem393259)). Qed.
Lemma lem393262 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term241 n P.
Proof. exact (h1). Qed.
Lemma lem393263 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term275 n P m) : term275 n P m.
Proof. exact (h1). Qed.
Lemma lem393264 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term493 n P m.
Proof. exact (h1). Qed.
Lemma lem393266 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem393279 (n : nat) (P : nat -> Prop) (m : nat) : (term250 n P m) = (term362 n P m).
Proof. exact (@lem17265 (term363 m n) (P m)). Qed.
Lemma lem393280 (n : nat) (P : nat -> Prop) : (term244 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem393279 n P m)). Qed.
Lemma lem393281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393318 (n : nat) (P : nat -> Prop) : (term241 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem393281) (@lem393280 n P)). Qed.
Lemma lem393319 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem393318 n P) (@lem393262 n P h1)). Qed.
Lemma lem393330 (n : nat) (P : nat -> Prop) (m : nat) : (term275 n P m) = (term359 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term30 P m)). Qed.
Lemma lem393342 (n : nat) (P : nat -> Prop) (m : nat) : (term493 n P m) = (term518 n P m).
Proof. exact (@lem17362 (term519 m n) (term520 P m)). Qed.
Lemma lem393371 (m : nat) (n : nat) : ((term321 m n) = (Peano.lt m n)) = (term365 m n).
Proof. exact (@lem17784 (term321 m n) (Peano.lt m n)). Qed.
Lemma lem393372 (m : nat) : (term322 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem393371 m n)). Qed.
Lemma lem393373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393374 (m : nat) : (term323 m) = (term367 m).
Proof. exact (MK_COMB (@lem393373) (@lem393372 m)). Qed.
Lemma lem393375 : term324 = term368.
Proof. exact (fun_ext (fun m : nat => @lem393374 m)). Qed.
Lemma lem393376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393377 : term301 = term369.
Proof. exact (MK_COMB (@lem393376) (@lem393375)). Qed.
Lemma lem393383 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem393384 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem393383 nat P Q). Qed.
Lemma lem393385 (m : nat) : (term374 m) = (term375 m).
Proof. exact (@lem393384 (term376 m) (term377 m)). Qed.
Lemma lem393386 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem393387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem393388 (m : nat) (n : nat) : (term380 m n) = (term381 m n).
Proof. exact (MK_COMB (@lem393387) (@lem393386 m n)). Qed.
Lemma lem393389 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem393390 (m : nat) (n : nat) : (term384 m n) = (term365 m n).
Proof. exact (MK_COMB (@lem393388 m n) (@lem393389 m n)). Qed.
Lemma lem393391 (m : nat) : (term385 m) = (term366 m).
Proof. exact (fun_ext (fun n : nat => @lem393390 m n)). Qed.
Lemma lem393392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393393 (m : nat) : (term374 m) = (term367 m).
Proof. exact (MK_COMB (@lem393392) (@lem393391 m)). Qed.
Lemma lem393394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem393395 (m : nat) : (term386 m) = (term387 m).
Proof. exact (MK_COMB (@lem393394) (@lem393393 m)). Qed.
Lemma lem393396 (m : nat) (n : nat) : (term378 m n) = (term379 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem393397 (m : nat) : (term388 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem393396 m n)). Qed.
Lemma lem393398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393399 (m : nat) : (term389 m) = (term390 m).
Proof. exact (MK_COMB (@lem393398) (@lem393397 m)). Qed.
Lemma lem393400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem393401 (m : nat) : (term391 m) = (term392 m).
Proof. exact (MK_COMB (@lem393400) (@lem393399 m)). Qed.
Lemma lem393402 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (eq_refl (term382 m n)). Qed.
Lemma lem393403 (m : nat) : (term393 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem393402 m n)). Qed.
Lemma lem393404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393405 (m : nat) : (term394 m) = (term395 m).
Proof. exact (MK_COMB (@lem393404) (@lem393403 m)). Qed.
Lemma lem393406 (m : nat) : (term375 m) = (term396 m).
Proof. exact (MK_COMB (@lem393401 m) (@lem393405 m)). Qed.
Lemma lem393407 (m : nat) : ((term374 m) = (term375 m)) = ((term367 m) = (term396 m)).
Proof. exact (MK_COMB (@lem393395 m) (@lem393406 m)). Qed.
Lemma lem393408 (m : nat) : (term367 m) = (term396 m).
Proof. exact (EQ_MP (@lem393407 m) (@lem393385 m)). Qed.
Lemma lem393505 : term368 = term397.
Proof. exact (fun_ext (fun m : nat => @lem393408 m)). Qed.
Lemma lem393506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393507 : term369 = term398.
Proof. exact (MK_COMB (@lem393506) (@lem393505)). Qed.
Lemma lem393509 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem393510 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem393509 nat P Q). Qed.
Lemma lem393511 : term399 = term400.
Proof. exact (@lem393510 term401 term402). Qed.
Lemma lem393512 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem393513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem393514 (m : nat) : (term404 m) = (term392 m).
Proof. exact (MK_COMB (@lem393513) (@lem393512 m)). Qed.
Lemma lem393515 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem393516 (m : nat) : (term406 m) = (term396 m).
Proof. exact (MK_COMB (@lem393514 m) (@lem393515 m)). Qed.
Lemma lem393517 : term407 = term397.
Proof. exact (fun_ext (fun m : nat => @lem393516 m)). Qed.
Lemma lem393518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393519 : term399 = term398.
Proof. exact (MK_COMB (@lem393518) (@lem393517)). Qed.
Lemma lem393520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem393521 : term408 = term409.
Proof. exact (MK_COMB (@lem393520) (@lem393519)). Qed.
Lemma lem393522 (m : nat) : (term403 m) = (term390 m).
Proof. exact (eq_refl (term403 m)). Qed.
Lemma lem393523 : term410 = term401.
Proof. exact (fun_ext (fun m : nat => @lem393522 m)). Qed.
Lemma lem393524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393525 : term411 = term412.
Proof. exact (MK_COMB (@lem393524) (@lem393523)). Qed.
Lemma lem393526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem393527 : term413 = term414.
Proof. exact (MK_COMB (@lem393526) (@lem393525)). Qed.
Lemma lem393528 (m : nat) : (term405 m) = (term395 m).
Proof. exact (eq_refl (term405 m)). Qed.
Lemma lem393529 : term415 = term402.
Proof. exact (fun_ext (fun m : nat => @lem393528 m)). Qed.
Lemma lem393530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393531 : term416 = term417.
Proof. exact (MK_COMB (@lem393530) (@lem393529)). Qed.
Lemma lem393532 : term400 = term418.
Proof. exact (MK_COMB (@lem393527) (@lem393531)). Qed.
Lemma lem393533 : (term399 = term400) = (term398 = term418).
Proof. exact (MK_COMB (@lem393521) (@lem393532)). Qed.
Lemma lem393534 : term398 = term418.
Proof. exact (EQ_MP (@lem393533) (@lem393511)). Qed.
Lemma lem393641 : term369 = term418.
Proof. exact (TRANS (@lem393507) (@lem393534)). Qed.
Lemma lem393642 : term301 = term418.
Proof. exact (TRANS (@lem393377) (@lem393641)). Qed.
Lemma lem393643 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem393642) (@lem393266 h1)). Qed.
Lemma lem393664 (n : nat) (P : nat -> Prop) (m : nat) : (term362 n P m) = (term362 n P m).
Proof. exact (eq_refl (term362 n P m)). Qed.
Lemma lem393665 (n : nat) (P : nat -> Prop) : (term464 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem393664 n P m)). Qed.
Lemma lem393666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393667 (n : nat) (P : nat -> Prop) : (term465 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem393666) (@lem393665 n P)). Qed.
Lemma lem393668 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem393667 n P) (@lem393319 n P h1)). Qed.
Lemma lem393684 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term275 n P m) : term359 n P m.
Proof. exact (EQ_MP (@lem393330 n P m) (@lem393263 n P m h1)). Qed.
Lemma lem393704 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term518 n P m.
Proof. exact (EQ_MP (@lem393342 n P m) (@lem393264 n P m h1)). Qed.
Lemma lem393736 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem393737 (m : nat) : (term377 m) = (term377 m).
Proof. exact (fun_ext (fun n : nat => @lem393736 m n)). Qed.
Lemma lem393738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393739 (m : nat) : (term395 m) = (term395 m).
Proof. exact (MK_COMB (@lem393738) (@lem393737 m)). Qed.
Lemma lem393740 : term402 = term402.
Proof. exact (fun_ext (fun m : nat => @lem393739 m)). Qed.
Lemma lem393741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393742 : term417 = term417.
Proof. exact (MK_COMB (@lem393741) (@lem393740)). Qed.
Lemma lem393761 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem393762 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem393761 m n)). Qed.
Lemma lem393763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393764 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem393763) (@lem393762 m)). Qed.
Lemma lem393765 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem393764 m)). Qed.
Lemma lem393766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393767 : term412 = term412.
Proof. exact (MK_COMB (@lem393766) (@lem393765)). Qed.
Lemma lem393768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem393769 : term414 = term414.
Proof. exact (MK_COMB (@lem393768) (@lem393767)). Qed.
Lemma lem393770 : term418 = term418.
Proof. exact (MK_COMB (@lem393769) (@lem393742)). Qed.
Lemma lem393771 (h1 : term301) : term418.
Proof. exact (EQ_MP (@lem393770) (@lem393643 h1)). Qed.
Lemma lem393773 (h1 : term301) : term412.
Proof. exact (proj1 (@lem393771 h1)). Qed.
Lemma lem393789 (n : nat) (P : nat -> Prop) (m : nat) : (term362 n P m) = (term362 n P m).
Proof. exact (eq_refl (term362 n P m)). Qed.
Lemma lem393790 (n : nat) (P : nat -> Prop) : (term464 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem393789 n P m)). Qed.
Lemma lem393791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393793 (n : nat) (P : nat -> Prop) : (term465 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem393791) (@lem393790 n P)). Qed.
Lemma lem393794 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem393793 n P) (@lem393668 n P h1)). Qed.
Lemma lem393809 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem393810 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem393809 m n)). Qed.
Lemma lem393811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393812 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem393811) (@lem393810 m)). Qed.
Lemma lem393813 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem393812 m)). Qed.
Lemma lem393814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393816 : term412 = term412.
Proof. exact (MK_COMB (@lem393814) (@lem393813)). Qed.
Lemma lem393817 (h1 : term301) : term412.
Proof. exact (EQ_MP (@lem393816) (@lem393773 h1)). Qed.
Lemma lem393857 (n : nat) (P : nat -> Prop) (m : nat) : (term362 n P m) = (term362 n P m).
Proof. exact (eq_refl (term362 n P m)). Qed.
Lemma lem393858 (n : nat) (P : nat -> Prop) : (term464 n P) = (term464 n P).
Proof. exact (fun_ext (fun m : nat => @lem393857 n P m)). Qed.
Lemma lem393859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393861 (n : nat) (P : nat -> Prop) : (term465 n P) = (term465 n P).
Proof. exact (MK_COMB (@lem393859) (@lem393858 n P)). Qed.
Lemma lem393862 (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term465 n P.
Proof. exact (EQ_MP (@lem393861 n P) (@lem393668 n P h1)). Qed.
Lemma lem393877 (m : nat) (n : nat) : (term379 m n) = (term379 m n).
Proof. exact (eq_refl (term379 m n)). Qed.
Lemma lem393878 (m : nat) : (term376 m) = (term376 m).
Proof. exact (fun_ext (fun n : nat => @lem393877 m n)). Qed.
Lemma lem393879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393880 (m : nat) : (term390 m) = (term390 m).
Proof. exact (MK_COMB (@lem393879) (@lem393878 m)). Qed.
Lemma lem393881 : term401 = term401.
Proof. exact (fun_ext (fun m : nat => @lem393880 m)). Qed.
Lemma lem393882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem393884 : term412 = term412.
Proof. exact (MK_COMB (@lem393882) (@lem393881)). Qed.
Lemma lem393885 (h1 : term301) : term412.
Proof. exact (EQ_MP (@lem393884) (@lem393773 h1)). Qed.
Lemma lem393914 (_8230 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term469 n P _8230.
Proof. exact (@lem393794 n P h1 _8230). Qed.
Lemma lem393915 (n : nat) (P : nat -> Prop) (_8230 : nat) : (term469 n P _8230) = (term362 n P _8230).
Proof. exact (eq_refl (term469 n P _8230)). Qed.
Lemma lem393920 (_8232 : nat) (h1 : term301) : term403 _8232.
Proof. exact (@lem393817 h1 _8232). Qed.
Lemma lem393921 (_8232 : nat) : (term403 _8232) = (term390 _8232).
Proof. exact (eq_refl (term403 _8232)). Qed.
Lemma lem393922 (_8232 : nat) (h1 : term301) : term390 _8232.
Proof. exact (EQ_MP (@lem393921 _8232) (@lem393920 _8232 h1)). Qed.
Lemma lem393923 (_8232 : nat) (_8233 : nat) (h1 : term301) : term378 _8232 _8233.
Proof. exact (@lem393922 _8232 h1 _8233). Qed.
Lemma lem393924 (_8232 : nat) (_8233 : nat) : (term378 _8232 _8233) = (term379 _8232 _8233).
Proof. exact (eq_refl (term378 _8232 _8233)). Qed.
Lemma lem393932 (_8236 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term469 n P _8236.
Proof. exact (@lem393862 n P h1 _8236). Qed.
Lemma lem393933 (n : nat) (P : nat -> Prop) (_8236 : nat) : (term469 n P _8236) = (term362 n P _8236).
Proof. exact (eq_refl (term469 n P _8236)). Qed.
Lemma lem393938 (_8238 : nat) (h1 : term301) : term403 _8238.
Proof. exact (@lem393885 h1 _8238). Qed.
Lemma lem393939 (_8238 : nat) : (term403 _8238) = (term390 _8238).
Proof. exact (eq_refl (term403 _8238)). Qed.
Lemma lem393940 (_8238 : nat) (h1 : term301) : term390 _8238.
Proof. exact (EQ_MP (@lem393939 _8238) (@lem393938 _8238 h1)). Qed.
Lemma lem393941 (_8238 : nat) (_8239 : nat) (h1 : term301) : term378 _8238 _8239.
Proof. exact (@lem393940 _8238 h1 _8239). Qed.
Lemma lem393942 (_8238 : nat) (_8239 : nat) : (term378 _8238 _8239) = (term379 _8238 _8239).
Proof. exact (eq_refl (term378 _8238 _8239)). Qed.
Lemma lem393957 (_8230 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term362 n P _8230.
Proof. exact (EQ_MP (@lem393915 n P _8230) (@lem393914 _8230 n P h1)). Qed.
Lemma lem393965 (_8232 : nat) (_8233 : nat) (h1 : term301) : term379 _8232 _8233.
Proof. exact (EQ_MP (@lem393924 _8232 _8233) (@lem393923 _8232 _8233 h1)). Qed.
Lemma lem393975 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term521 P m.
Proof. exact (proj2 (@lem393704 n P m h1)). Qed.
Lemma lem393985 (_8236 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term362 n P _8236.
Proof. exact (EQ_MP (@lem393933 n P _8236) (@lem393932 _8236 n P h1)). Qed.
Lemma lem393993 (_8238 : nat) (_8239 : nat) (h1 : term301) : term379 _8238 _8239.
Proof. exact (EQ_MP (@lem393942 _8238 _8239) (@lem393941 _8238 _8239 h1)). Qed.
Lemma lem394003 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term521 P m.
Proof. exact (proj2 (@lem393704 n P m h1)). Qed.
Lemma lem394007 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term519 m n.
Proof. exact (proj1 (@lem393704 n P m h1)). Qed.
Lemma lem394008 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term522 m n.
Proof. exact (fun h0 : term523 m n => @lem394007 n P m h1). Qed.
Lemma lem394010 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394011 (m : nat) (n : nat) : (term522 m n) = (term519 m n).
Proof. exact (@lem394010 (term519 m n)). Qed.
Lemma lem394012 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term519 m n.
Proof. exact (EQ_MP (@lem394011 m n) (@lem394008 n P m h1)). Qed.
Lemma lem394014 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem394015 (_8232 : nat) (_8233 : nat) : (term379 _8232 _8233) = (term473 _8232 _8233).
Proof. exact (@lem394014 (term431 _8232 _8233) (term321 _8232 _8233)). Qed.
Lemma lem394017 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem394018 (_8232 : nat) (_8233 : nat) : (term436 _8232 _8233) = (Peano.lt _8232 _8233).
Proof. exact (@lem394017 (Peano.lt _8232 _8233)). Qed.
Lemma lem394019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394020 (_8232 : nat) (_8233 : nat) : (term437 _8232 _8233) = (term438 _8232 _8233).
Proof. exact (MK_COMB (@lem394019) (@lem394018 _8232 _8233)). Qed.
Lemma lem394021 (_8232 : nat) (_8233 : nat) : (term321 _8232 _8233) = (term321 _8232 _8233).
Proof. exact (eq_refl (term321 _8232 _8233)). Qed.
Lemma lem394022 (_8232 : nat) (_8233 : nat) : (term473 _8232 _8233) = (term474 _8232 _8233).
Proof. exact (MK_COMB (@lem394020 _8232 _8233) (@lem394021 _8232 _8233)). Qed.
Lemma lem394023 (_8232 : nat) (_8233 : nat) : (term379 _8232 _8233) = (term474 _8232 _8233).
Proof. exact (TRANS (@lem394015 _8232 _8233) (@lem394022 _8232 _8233)). Qed.
Lemma lem394026 (_8232 : nat) (_8233 : nat) (h1 : term301) : term474 _8232 _8233.
Proof. exact (EQ_MP (@lem394023 _8232 _8233) (@lem393965 _8232 _8233 h1)). Qed.
Lemma lem394027 (m : nat) (n : nat) (h1 : term301) : term524 m n.
Proof. exact (@lem394026 (S m) n h1). Qed.
Lemma lem394030 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term525 m n.
Proof. exact (@lem394027 m n h1 (@lem394012 n P m h2)). Qed.
Lemma lem394031 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term526 m n.
Proof. exact (fun h0 : term527 m n => @lem394030 n P m h1 h2). Qed.
Lemma lem394033 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394034 (m : nat) (n : nat) : (term526 m n) = (term525 m n).
Proof. exact (@lem394033 (term525 m n)). Qed.
Lemma lem394035 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term525 m n.
Proof. exact (EQ_MP (@lem394034 m n) (@lem394031 n P m h1 h2)). Qed.
Lemma lem394041 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem394042 (P : nat -> Prop) (_8230 : nat) (n : nat) : (term362 n P _8230) = (term479 P _8230 n).
Proof. exact (@lem394041 (P _8230) (term439 _8230 n)). Qed.
Lemma lem394048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem394049 (P : nat -> Prop) (_8230 : nat) (n : nat) : (term480 n P _8230) = (term481 P _8230 n).
Proof. exact (MK_COMB (@lem394048) (@lem394042 P _8230 n)). Qed.
Lemma lem394055 (P : nat -> Prop) (_8230 : nat) (n : nat) : (term479 P _8230 n) = (term479 P _8230 n).
Proof. exact (eq_refl (term479 P _8230 n)). Qed.
Lemma lem394056 (P : nat -> Prop) (_8230 : nat) (n : nat) : ((term362 n P _8230) = (term479 P _8230 n)) = ((term479 P _8230 n) = (term479 P _8230 n)).
Proof. exact (MK_COMB (@lem394049 P _8230 n) (@lem394055 P _8230 n)). Qed.
Lemma lem394058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem394059 (x : Prop) : (x = x) = True.
Proof. exact (@lem394058 Prop x). Qed.
Lemma lem394060 (P : nat -> Prop) (_8230 : nat) (n : nat) : ((term479 P _8230 n) = (term479 P _8230 n)) = True.
Proof. exact (@lem394059 (term479 P _8230 n)). Qed.
Lemma lem394061 (P : nat -> Prop) (_8230 : nat) (n : nat) : ((term362 n P _8230) = (term479 P _8230 n)) = True.
Proof. exact (TRANS (@lem394056 P _8230 n) (@lem394060 P _8230 n)). Qed.
Lemma lem394062 (P : nat -> Prop) (_8230 : nat) (n : nat) : True = ((term362 n P _8230) = (term479 P _8230 n)).
Proof. exact (SYM (@lem394061 P _8230 n)). Qed.
Lemma lem394063 (P : nat -> Prop) (_8230 : nat) (n : nat) : (term362 n P _8230) = (term479 P _8230 n).
Proof. exact (EQ_MP (@lem394062 P _8230 n) (@lem0)). Qed.
Lemma lem394064 (_8230 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term479 P _8230 n.
Proof. exact (EQ_MP (@lem394063 P _8230 n) (@lem393957 _8230 n P h1)). Qed.
Lemma lem394066 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem394067 (n : nat) (P : nat -> Prop) (_8230 : nat) : (term479 P _8230 n) = (term482 n P _8230).
Proof. exact (@lem394066 (term439 _8230 n) (P _8230)). Qed.
Lemma lem394069 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem394070 (_8230 : nat) (n : nat) : (term483 _8230 n) = (term363 _8230 n).
Proof. exact (@lem394069 (term363 _8230 n)). Qed.
Lemma lem394071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394072 (_8230 : nat) (n : nat) : (term484 _8230 n) = (term485 _8230 n).
Proof. exact (MK_COMB (@lem394071) (@lem394070 _8230 n)). Qed.
Lemma lem394073 (P : nat -> Prop) (_8230 : nat) : (P _8230) = (P _8230).
Proof. exact (eq_refl (P _8230)). Qed.
Lemma lem394074 (n : nat) (P : nat -> Prop) (_8230 : nat) : (term482 n P _8230) = (term250 n P _8230).
Proof. exact (MK_COMB (@lem394072 _8230 n) (@lem394073 P _8230)). Qed.
Lemma lem394075 (n : nat) (P : nat -> Prop) (_8230 : nat) : (term479 P _8230 n) = (term250 n P _8230).
Proof. exact (TRANS (@lem394067 n P _8230) (@lem394074 n P _8230)). Qed.
Lemma lem394078 (_8230 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term250 n P _8230.
Proof. exact (EQ_MP (@lem394075 n P _8230) (@lem394064 _8230 n P h1)). Qed.
Lemma lem394079 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term528 n P m.
Proof. exact (@lem394078 (term529 m) n P h1). Qed.
Lemma lem394082 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term520 P m.
Proof. exact (@lem394079 m n P h2 (@lem394035 n P m h1 h3)). Qed.
Lemma lem394083 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term530 P m.
Proof. exact (fun h0 : term521 P m => @lem394082 n P m h1 h2 h3). Qed.
Lemma lem394085 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394086 (P : nat -> Prop) (m : nat) : (term530 P m) = (term520 P m).
Proof. exact (@lem394085 (term520 P m)). Qed.
Lemma lem394087 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term520 P m.
Proof. exact (EQ_MP (@lem394086 P m) (@lem394083 n P m h1 h2 h3)). Qed.
Lemma lem394090 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem394092 (P : nat -> Prop) (m : nat) : (term521 P m) = (term531 P m).
Proof. exact (@lem394090 (term520 P m)). Qed.
Lemma lem394095 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term531 P m.
Proof. exact (EQ_MP (@lem394092 P m) (@lem393975 n P m h1)). Qed.
Lemma lem394098 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : False.
Proof. exact (@lem394095 n P m h3 (@lem394087 n P m h1 h2 h3)). Qed.
Lemma lem394099 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term180.
Proof. exact (fun h0 : ~ False => @lem394098 n P m h1 h2 h3). Qed.
Lemma lem394101 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394102 : term180 = False.
Proof. exact (@lem394101 False). Qed.
Lemma lem394103 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : False.
Proof. exact (EQ_MP (@lem394102) (@lem394099 n P m h1 h2 h3)). Qed.
Lemma lem394105 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term519 m n.
Proof. exact (proj1 (@lem393704 n P m h1)). Qed.
Lemma lem394106 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term522 m n.
Proof. exact (fun h0 : term523 m n => @lem394105 n P m h1). Qed.
Lemma lem394108 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394109 (m : nat) (n : nat) : (term522 m n) = (term519 m n).
Proof. exact (@lem394108 (term519 m n)). Qed.
Lemma lem394110 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term519 m n.
Proof. exact (EQ_MP (@lem394109 m n) (@lem394106 n P m h1)). Qed.
Lemma lem394112 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem394113 (_8238 : nat) (_8239 : nat) : (term379 _8238 _8239) = (term473 _8238 _8239).
Proof. exact (@lem394112 (term431 _8238 _8239) (term321 _8238 _8239)). Qed.
Lemma lem394115 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem394116 (_8238 : nat) (_8239 : nat) : (term436 _8238 _8239) = (Peano.lt _8238 _8239).
Proof. exact (@lem394115 (Peano.lt _8238 _8239)). Qed.
Lemma lem394117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394118 (_8238 : nat) (_8239 : nat) : (term437 _8238 _8239) = (term438 _8238 _8239).
Proof. exact (MK_COMB (@lem394117) (@lem394116 _8238 _8239)). Qed.
Lemma lem394119 (_8238 : nat) (_8239 : nat) : (term321 _8238 _8239) = (term321 _8238 _8239).
Proof. exact (eq_refl (term321 _8238 _8239)). Qed.
Lemma lem394120 (_8238 : nat) (_8239 : nat) : (term473 _8238 _8239) = (term474 _8238 _8239).
Proof. exact (MK_COMB (@lem394118 _8238 _8239) (@lem394119 _8238 _8239)). Qed.
Lemma lem394121 (_8238 : nat) (_8239 : nat) : (term379 _8238 _8239) = (term474 _8238 _8239).
Proof. exact (TRANS (@lem394113 _8238 _8239) (@lem394120 _8238 _8239)). Qed.
Lemma lem394124 (_8238 : nat) (_8239 : nat) (h1 : term301) : term474 _8238 _8239.
Proof. exact (EQ_MP (@lem394121 _8238 _8239) (@lem393993 _8238 _8239 h1)). Qed.
Lemma lem394125 (m : nat) (n : nat) (h1 : term301) : term524 m n.
Proof. exact (@lem394124 (S m) n h1). Qed.
Lemma lem394128 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term525 m n.
Proof. exact (@lem394125 m n h1 (@lem394110 n P m h2)). Qed.
Lemma lem394129 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term526 m n.
Proof. exact (fun h0 : term527 m n => @lem394128 n P m h1 h2). Qed.
Lemma lem394131 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394132 (m : nat) (n : nat) : (term526 m n) = (term525 m n).
Proof. exact (@lem394131 (term525 m n)). Qed.
Lemma lem394133 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term493 n P m) : term525 m n.
Proof. exact (EQ_MP (@lem394132 m n) (@lem394129 n P m h1 h2)). Qed.
Lemma lem394139 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem394140 (P : nat -> Prop) (_8236 : nat) (n : nat) : (term362 n P _8236) = (term479 P _8236 n).
Proof. exact (@lem394139 (P _8236) (term439 _8236 n)). Qed.
Lemma lem394146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem394147 (P : nat -> Prop) (_8236 : nat) (n : nat) : (term480 n P _8236) = (term481 P _8236 n).
Proof. exact (MK_COMB (@lem394146) (@lem394140 P _8236 n)). Qed.
Lemma lem394153 (P : nat -> Prop) (_8236 : nat) (n : nat) : (term479 P _8236 n) = (term479 P _8236 n).
Proof. exact (eq_refl (term479 P _8236 n)). Qed.
Lemma lem394154 (P : nat -> Prop) (_8236 : nat) (n : nat) : ((term362 n P _8236) = (term479 P _8236 n)) = ((term479 P _8236 n) = (term479 P _8236 n)).
Proof. exact (MK_COMB (@lem394147 P _8236 n) (@lem394153 P _8236 n)). Qed.
Lemma lem394156 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem394157 (x : Prop) : (x = x) = True.
Proof. exact (@lem394156 Prop x). Qed.
Lemma lem394158 (P : nat -> Prop) (_8236 : nat) (n : nat) : ((term479 P _8236 n) = (term479 P _8236 n)) = True.
Proof. exact (@lem394157 (term479 P _8236 n)). Qed.
Lemma lem394159 (P : nat -> Prop) (_8236 : nat) (n : nat) : ((term362 n P _8236) = (term479 P _8236 n)) = True.
Proof. exact (TRANS (@lem394154 P _8236 n) (@lem394158 P _8236 n)). Qed.
Lemma lem394160 (P : nat -> Prop) (_8236 : nat) (n : nat) : True = ((term362 n P _8236) = (term479 P _8236 n)).
Proof. exact (SYM (@lem394159 P _8236 n)). Qed.
Lemma lem394161 (P : nat -> Prop) (_8236 : nat) (n : nat) : (term362 n P _8236) = (term479 P _8236 n).
Proof. exact (EQ_MP (@lem394160 P _8236 n) (@lem0)). Qed.
Lemma lem394162 (_8236 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term479 P _8236 n.
Proof. exact (EQ_MP (@lem394161 P _8236 n) (@lem393985 _8236 n P h1)). Qed.
Lemma lem394164 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem394165 (n : nat) (P : nat -> Prop) (_8236 : nat) : (term479 P _8236 n) = (term482 n P _8236).
Proof. exact (@lem394164 (term439 _8236 n) (P _8236)). Qed.
Lemma lem394167 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem394168 (_8236 : nat) (n : nat) : (term483 _8236 n) = (term363 _8236 n).
Proof. exact (@lem394167 (term363 _8236 n)). Qed.
Lemma lem394169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394170 (_8236 : nat) (n : nat) : (term484 _8236 n) = (term485 _8236 n).
Proof. exact (MK_COMB (@lem394169) (@lem394168 _8236 n)). Qed.
Lemma lem394171 (P : nat -> Prop) (_8236 : nat) : (P _8236) = (P _8236).
Proof. exact (eq_refl (P _8236)). Qed.
Lemma lem394172 (n : nat) (P : nat -> Prop) (_8236 : nat) : (term482 n P _8236) = (term250 n P _8236).
Proof. exact (MK_COMB (@lem394170 _8236 n) (@lem394171 P _8236)). Qed.
Lemma lem394173 (n : nat) (P : nat -> Prop) (_8236 : nat) : (term479 P _8236 n) = (term250 n P _8236).
Proof. exact (TRANS (@lem394165 n P _8236) (@lem394172 n P _8236)). Qed.
Lemma lem394176 (_8236 : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term250 n P _8236.
Proof. exact (EQ_MP (@lem394173 n P _8236) (@lem394162 _8236 n P h1)). Qed.
Lemma lem394177 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term528 n P m.
Proof. exact (@lem394176 (term529 m) n P h1). Qed.
Lemma lem394180 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term520 P m.
Proof. exact (@lem394177 m n P h2 (@lem394133 n P m h1 h3)). Qed.
Lemma lem394181 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term530 P m.
Proof. exact (fun h0 : term521 P m => @lem394180 n P m h1 h2 h3). Qed.
Lemma lem394183 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394184 (P : nat -> Prop) (m : nat) : (term530 P m) = (term520 P m).
Proof. exact (@lem394183 (term520 P m)). Qed.
Lemma lem394185 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term520 P m.
Proof. exact (EQ_MP (@lem394184 P m) (@lem394181 n P m h1 h2 h3)). Qed.
Lemma lem394188 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem394190 (P : nat -> Prop) (m : nat) : (term521 P m) = (term531 P m).
Proof. exact (@lem394188 (term520 P m)). Qed.
Lemma lem394193 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term493 n P m) : term531 P m.
Proof. exact (EQ_MP (@lem394190 P m) (@lem394003 n P m h1)). Qed.
Lemma lem394196 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : False.
Proof. exact (@lem394193 n P m h3 (@lem394185 n P m h1 h2 h3)). Qed.
Lemma lem394197 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : term180.
Proof. exact (fun h0 : ~ False => @lem394196 n P m h1 h2 h3). Qed.
Lemma lem394199 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem394200 : term180 = False.
Proof. exact (@lem394199 False). Qed.
Lemma lem394201 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) : False.
Proof. exact (EQ_MP (@lem394200) (@lem394197 n P m h1 h2 h3)). Qed.
Lemma lem394202 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term301) (h2 : term241 n P) (h3 : term493 n P m) (h4 : term275 n P m) : False.
Proof. exact (or_elim (@lem393684 n P m h4) (fun h0 : term431 m n => @lem394103 n P m h1 h2 h3) (fun h0 : term30 P m => @lem394201 n P m h1 h2 h3)). Qed.
Lemma lem394203 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term275 n P m) : term299.
Proof. exact (fun h0 : term301 => @lem394202 n P m h0 h1 h2 h3). Qed.
Lemma lem394204 : term299 = term300.
Proof. exact (@lem69 term301). Qed.
Lemma lem394205 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term275 n P m) : term300.
Proof. exact (EQ_MP (@lem394204) (@lem394203 n P m h1 h2 h3)). Qed.
Lemma lem394206 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term275 n P m) : term304.
Proof. exact (fun h0 : term327 => @lem394205 n P m h1 h2 h3). Qed.
Lemma lem394207 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term275 n P m) : term500 n P m.
Proof. exact (fun h0 : term493 n P m => @lem394206 n P m h1 h0 h2). Qed.
Lemma lem394208 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) : term502 n P m.
Proof. exact (fun h0 : term275 n P m => @lem394207 n P m h1 h0). Qed.
Lemma lem394209 (n : nat) (P : nat -> Prop) (m : nat) : term504 n P m.
Proof. exact (fun h0 : term241 n P => @lem394208 m n P h0). Qed.
Lemma lem394210 (n : nat) (P : nat -> Prop) (m : nat) : term505 n P m.
Proof. exact (fun h0 : term188 P => @lem394209 n P m). Qed.
Lemma lem394215 (P : nat -> Prop) (m : nat) : term509 P m.
Proof. exact (fun n : nat => @lem394210 n P m). Qed.
Lemma lem394220 (m : nat) : term513 m.
Proof. exact (fun P : nat -> Prop => @lem394215 P m). Qed.
Lemma lem394225 : term517.
Proof. exact (fun m : nat => @lem394220 m). Qed.
Lemma lem394226 : term516.
Proof. exact (EQ_MP (@lem393260) (@lem394225)). Qed.
Lemma lem394227 (m : nat) : term532 m.
Proof. exact (@lem394226 m). Qed.
Lemma lem394228 (m : nat) : (term532 m) = (term512 m).
Proof. exact (eq_refl (term532 m)). Qed.
Lemma lem394229 (m : nat) : term512 m.
Proof. exact (EQ_MP (@lem394228 m) (@lem394227 m)). Qed.
Lemma lem394230 (m : nat) (P : nat -> Prop) : term533 m P.
Proof. exact (@lem394229 m P). Qed.
Lemma lem394231 (P : nat -> Prop) (m : nat) : (term533 m P) = (term508 P m).
Proof. exact (eq_refl (term533 m P)). Qed.
Lemma lem394232 (P : nat -> Prop) (m : nat) : term508 P m.
Proof. exact (EQ_MP (@lem394231 P m) (@lem394230 m P)). Qed.
Lemma lem394233 (P : nat -> Prop) (m : nat) (n : nat) : term534 P m n.
Proof. exact (@lem394232 P m n). Qed.
Lemma lem394234 (n : nat) (P : nat -> Prop) (m : nat) : (term534 P m n) = (term494 n P m).
Proof. exact (eq_refl (term534 P m n)). Qed.
Lemma lem394235 (n : nat) (P : nat -> Prop) (m : nat) : term494 n P m.
Proof. exact (EQ_MP (@lem394234 n P m) (@lem394233 P m n)). Qed.
Lemma lem394237 (n : nat) (P : nat -> Prop) (m : nat) : term494 n P m.
Proof. exact (@lem393044 n P m (@lem394235 n P m)). Qed.
Lemma lem394238 (n : nat) (m : nat) (P : nat -> Prop) (h1 : term188 P) : term503 n P m.
Proof. exact (@lem394237 n P m (@lem389880 P h1)). Qed.
Lemma lem394239 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term501 n P m.
Proof. exact (@lem394238 n m P h2 (@lem389882 n P h1)). Qed.
Lemma lem394240 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term188 P) (h3 : term275 n P m) : term499 n P m.
Proof. exact (@lem394239 m n P h1 h2 (@lem389930 n P m h3)). Qed.
Lemma lem394241 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term188 P) (h4 : term275 n P m) : term303.
Proof. exact (@lem394240 n P m h1 h3 h4 (@lem393029 n P m h2)). Qed.
Lemma lem394242 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term188 P) (h4 : term275 n P m) : term299.
Proof. exact (@lem394241 n P m h1 h2 h3 h4 (@lem91530)). Qed.
Lemma lem394243 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term188 P) (h4 : term275 n P m) : False.
Proof. exact (@lem394242 n P m h1 h2 h3 h4 (@lem91415)). Qed.
Lemma lem394244 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term188 P) (h4 : term275 n P m) : (term493 n P m) = False.
Proof. exact (prop_ext (fun h5 : term493 n P m => @lem394243 n P m h1 h2 h3 h4) (fun h5 : False => @lem393029 n P m h2)). Qed.
Lemma lem394245 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term493 n P m) (h3 : term188 P) (h4 : term275 n P m) : False.
Proof. exact (EQ_MP (@lem394244 n P m h1 h2 h3 h4) (@lem393029 n P m h2)). Qed.
Lemma lem394246 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term188 P) (h3 : term275 n P m) : term492 n P m.
Proof. exact (fun h0 : term493 n P m => @lem394245 n P m h1 h0 h2 h3). Qed.
Lemma lem394247 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term241 n P) (h2 : term188 P) (h3 : term275 n P m) : term279 n P m.
Proof. exact (EQ_MP (@lem393028 n P m) (@lem394246 n P m h1 h2 h3)). Qed.
Lemma lem394248 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term281 n P m.
Proof. exact (fun h0 : term275 n P m => @lem394247 n P m h1 h2 h0). Qed.
Lemma lem394253 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term285 n P.
Proof. exact (fun m : nat => @lem394248 m n P h1 h2). Qed.
Lemma lem394254 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term287 n P.
Proof. exact (conj (@lem393024 n P h1 h2) (@lem394253 n P h1 h2)). Qed.
Lemma lem394255 (n : nat) (P : nat -> Prop) (h1 : term241 n P) (h2 : term188 P) : term240 n P.
Proof. exact (@lem389929 n P (@lem394254 n P h1 h2)). Qed.
Lemma lem394256 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term256 n P m.
Proof. exact (fun h0 : term250 n P m => @lem392101 n P m h1 h2 h0). Qed.
Lemma lem394261 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term260 n P.
Proof. exact (fun m : nat => @lem394256 m n P h1 h2). Qed.
Lemma lem394262 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term262 n P.
Proof. exact (conj (@lem390804 n P h1 h2) (@lem394261 n P h1 h2)). Qed.
Lemma lem394263 (n : nat) (P : nat -> Prop) (h1 : term240 n P) (h2 : term188 P) : term241 n P.
Proof. exact (@lem389905 n P (@lem394262 n P h1 h2)). Qed.
Lemma lem394264 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term535 n P.
Proof. exact (fun h0 : term241 n P => @lem394255 n P h0 h1). Qed.
Lemma lem394265 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term536 n P.
Proof. exact (fun h0 : term240 n P => @lem394263 n P h0 h1). Qed.
Lemma lem394266 (n : nat) (P : nat -> Prop) (h1 : term188 P) : term537 n P.
Proof. exact (conj (@lem394265 n P h1) (@lem394264 n P h1)). Qed.
Lemma lem394267 (n : nat) (P : nat -> Prop) : (term537 n P) = ((term240 n P) = (term241 n P)).
Proof. exact (@lem32 (term240 n P) (term241 n P)). Qed.
Lemma lem394268 (n : nat) (P : nat -> Prop) (h1 : term188 P) : (term240 n P) = (term241 n P).
Proof. exact (EQ_MP (@lem394267 n P) (@lem394266 n P h1)). Qed.
Lemma lem394269 (n : nat) (P : nat -> Prop) : term538 n P.
Proof. exact (fun h0 : term188 P => @lem394268 n P h0). Qed.
Lemma lem394290 {A : Type'} (P : A -> Prop) : term539 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem394291 {A : Type'} (P : A -> Prop) : (term539 A P) = (term540 A P).
Proof. exact (eq_refl (term539 A P)). Qed.
Lemma lem394292 {A : Type'} (P : A -> Prop) : term540 A P.
Proof. exact (EQ_MP (@lem394291 A P) (@lem394290 A P)). Qed.
Lemma lem394293 {A : Type'} (P : A -> Prop) (Q : Prop) : term541 A P Q.
Proof. exact (@lem394292 A P Q). Qed.
Lemma lem394294 {A : Type'} (P : A -> Prop) (Q : Prop) : (term541 A P Q) = ((term542 A P Q) = (term543 A P Q)).
Proof. exact (eq_refl (term541 A P Q)). Qed.
Lemma lem394296 {A : Type'} (h1 : term544 A) : term544 A.
Proof. exact (h1). Qed.
Lemma lem394297 {A : Type'} (P : A -> Prop) (h1 : term544 A) : term545 A P.
Proof. exact (@lem394296 A h1 P). Qed.
Lemma lem394298 {A : Type'} (P : A -> Prop) : (term545 A P) = (term546 A P).
Proof. exact (eq_refl (term545 A P)). Qed.
Lemma lem394299 {A : Type'} (P : A -> Prop) (h1 : term544 A) : term546 A P.
Proof. exact (EQ_MP (@lem394298 A P) (@lem394297 A P h1)). Qed.
Lemma lem394300 {A : Type'} (P : A -> Prop) (x : A) (h1 : term544 A) : term547 A P x.
Proof. exact (@lem394299 A P h1 x). Qed.
Lemma lem394301 {A : Type'} (P : A -> Prop) (x : A) : (term547 A P x) = (term548 A P x).
Proof. exact (eq_refl (term547 A P x)). Qed.
Lemma lem394302 {A : Type'} (P : A -> Prop) (x : A) (h1 : term544 A) : term548 A P x.
Proof. exact (EQ_MP (@lem394301 A P x) (@lem394300 A P x h1)). Qed.
Lemma lem394303 {A : Type'} (P : A -> Prop) (x : A) (h1 : term549 A P x) : term549 A P x.
Proof. exact (h1). Qed.
Lemma lem394304 {A : Type'} (P : A -> Prop) (x : A) (h1 : term549 A P x) (h2 : term544 A) : (@ε A P) = x.
Proof. exact (@lem394302 A P x h2 (@lem394303 A P x h1)). Qed.
Lemma lem394305 {A : Type'} (P : A -> Prop) (x : A) (h1 : term549 A P x) : term550 A P x.
Proof. exact (fun h0 : term544 A => @lem394304 A P x h1 h0). Qed.
Lemma lem394306 {A : Type'} (h1 : term544 A) : term544 A.
Proof. exact (h1). Qed.
Lemma lem394307 {A : Type'} (P : A -> Prop) (x : A) (h1 : term549 A P x) (h2 : term544 A) : (@ε A P) = x.
Proof. exact (@lem394305 A P x h1 (@lem394306 A h2)). Qed.
Lemma lem394308 {A : Type'} (P : A -> Prop) (x : A) (h1 : term544 A) : term548 A P x.
Proof. exact (fun h0 : term549 A P x => @lem394307 A P x h0 h1). Qed.
Lemma lem394309 {A : Type'} (P : A -> Prop) (h1 : term544 A) : term546 A P.
Proof. exact (fun x : A => @lem394308 A P x h1). Qed.
Lemma lem394310 {A : Type'} (h1 : term544 A) : term544 A.
Proof. exact (fun P : A -> Prop => @lem394309 A P h1). Qed.
Lemma lem394311 {A : Type'} : term551 A.
Proof. exact (fun h0 : term544 A => @lem394310 A h0). Qed.
Lemma lem394312 {A : Type'} : term544 A.
Proof. exact (@lem394311 A (@lem9522 A)). Qed.
Lemma lem394313 {A : Type'} (P : A -> Prop) : term545 A P.
Proof. exact (@lem394312 A P). Qed.
Lemma lem394314 {A : Type'} (P : A -> Prop) : (term545 A P) = (term546 A P).
Proof. exact (eq_refl (term545 A P)). Qed.
Lemma lem394315 {A : Type'} (P : A -> Prop) : term546 A P.
Proof. exact (EQ_MP (@lem394314 A P) (@lem394313 A P)). Qed.
Lemma lem394316 {A : Type'} (P : A -> Prop) (x : A) : term547 A P x.
Proof. exact (@lem394315 A P x). Qed.
Lemma lem394317 {A : Type'} (P : A -> Prop) (x : A) : (term547 A P x) = (term548 A P x).
Proof. exact (eq_refl (term547 A P x)). Qed.
Lemma lem394329 {A : Type'} (P : A -> Prop) (x : A) : term552 A P x.
Proof. exact (@lem9784 (P x)). Qed.
Lemma lem394330 {A : Type'} (P : A -> Prop) (x : A) : (term552 A P x) = (term553 A P x).
Proof. exact (eq_refl (term552 A P x)). Qed.
Lemma lem394331 {A : Type'} (P : A -> Prop) (x : A) : term553 A P x.
Proof. exact (EQ_MP (@lem394330 A P x) (@lem394329 A P x)). Qed.
Lemma lem394332 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem394333 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem394334 {A : Type'} (P : A -> Prop) : term555 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem394335 {A : Type'} (P : A -> Prop) : (term555 A P) = (term556 A P).
Proof. exact (eq_refl (term555 A P)). Qed.
Lemma lem394336 {A : Type'} (P : A -> Prop) : term556 A P.
Proof. exact (EQ_MP (@lem394335 A P) (@lem394334 A P)). Qed.
Lemma lem394337 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term557 A P Q.
Proof. exact (@lem394336 A P Q). Qed.
Lemma lem394338 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term557 A P Q) = ((term370 A P Q) = (term371 A P Q)).
Proof. exact (eq_refl (term557 A P Q)). Qed.
Lemma lem394340 {A B : Type'} (P : type1413 A B) : term558 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem394341 {A B : Type'} (P : type1413 A B) : (term558 A B P) = ((term148 A B P) = (term149 A B P)).
Proof. exact (eq_refl (term558 A B P)). Qed.
Lemma lem394343 {A : Type'} : term559 A.
Proof. exact (@lem75635 A). Qed.
Lemma lem394344 {A : Type'} (x : A) : term560 A x.
Proof. exact (@lem394343 A x). Qed.
Lemma lem394345 {A : Type'} (x : A) : (term560 A x) = (term561 A x).
Proof. exact (eq_refl (term560 A x)). Qed.
Lemma lem394346 {A : Type'} (x : A) : term561 A x.
Proof. exact (EQ_MP (@lem394345 A x) (@lem394344 A x)). Qed.
Lemma lem394347 {A : Type'} (x : A) (g : A -> A) : term562 A x g.
Proof. exact (@lem394346 A x (term563 A g)). Qed.
Lemma lem394348 {A : Type'} (x : A) (g : A -> A) : (term562 A x g) = (term564 A x g).
Proof. exact (eq_refl (term562 A x g)). Qed.
Lemma lem394349 {A : Type'} (x : A) (g : A -> A) : term564 A x g.
Proof. exact (EQ_MP (@lem394348 A x g) (@lem394347 A x g)). Qed.
Lemma lem394350 {A : Type'} (g : A -> A) : term565 A g.
Proof. exact (fun x : A => @lem394349 A x g). Qed.
Lemma lem394354 {A B : Type'} (P : type1413 A B) : (term148 A B P) = (term149 A B P).
Proof. exact (EQ_MP (@lem394341 A B P) (@lem394340 A B P)). Qed.
Lemma lem394355 {A : Type'} (P : type1382 A) : (term566 A P) = (term567 A P).
Proof. exact (@lem394354 A (nat -> A) P). Qed.
Lemma lem394356 {A : Type'} (g : A -> A) : (term568 A g) = (term569 A g).
Proof. exact (@lem394355 A (term570 A g)). Qed.
Lemma lem394357 {A : Type'} (x : A) (g : A -> A) : (term571 A g x) = (term572 A x g).
Proof. exact (eq_refl (term571 A g x)). Qed.
Lemma lem394358 {A : Type'} (fn : nat -> A) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem394359 {A : Type'} (x : A) (g : A -> A) (fn : nat -> A) : (term573 A g x fn) = (term574 A x g fn).
Proof. exact (MK_COMB (@lem394357 A x g) (@lem394358 A fn)). Qed.
Lemma lem394360 {A : Type'} (x : A) (g : A -> A) (fn : nat -> A) : (term574 A x g fn) = (term575 A x g fn).
Proof. exact (eq_refl (term574 A x g fn)). Qed.
Lemma lem394361 {A : Type'} (x : A) (g : A -> A) (fn : nat -> A) : (term573 A g x fn) = (term575 A x g fn).
Proof. exact (TRANS (@lem394359 A x g fn) (@lem394360 A x g fn)). Qed.
Lemma lem394362 {A : Type'} (x : A) (g : A -> A) : (term576 A g x) = (term572 A x g).
Proof. exact (fun_ext (fun fn : nat -> A => @lem394361 A x g fn)). Qed.
Lemma lem394363 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem394364 {A : Type'} (x : A) (g : A -> A) : (term577 A g x) = (term564 A x g).
Proof. exact (MK_COMB (@lem394363 A) (@lem394362 A x g)). Qed.
Lemma lem394365 {A : Type'} (g : A -> A) : (term578 A g) = (term579 A g).
Proof. exact (fun_ext (fun x : A => @lem394364 A x g)). Qed.
Lemma lem394366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394367 {A : Type'} (g : A -> A) : (term568 A g) = (term565 A g).
Proof. exact (MK_COMB (@lem394366 A) (@lem394365 A g)). Qed.
Lemma lem394368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem394369 {A : Type'} (g : A -> A) : (term580 A g) = (term581 A g).
Proof. exact (MK_COMB (@lem394368) (@lem394367 A g)). Qed.
Lemma lem394370 {A : Type'} (x : A) (g : A -> A) : (term571 A g x) = (term572 A x g).
Proof. exact (eq_refl (term571 A g x)). Qed.
Lemma lem394371 {A : Type'} (fn : type1423 A) (x : A) : (fn x) = (fn x).
Proof. exact (eq_refl (fn x)). Qed.
Lemma lem394372 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term582 A g fn x) = (term583 A g fn x).
Proof. exact (MK_COMB (@lem394370 A x g) (@lem394371 A fn x)). Qed.
Lemma lem394373 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term583 A g fn x) = (term584 A g fn x).
Proof. exact (eq_refl (term583 A g fn x)). Qed.
Lemma lem394374 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term582 A g fn x) = (term584 A g fn x).
Proof. exact (TRANS (@lem394372 A g fn x) (@lem394373 A g fn x)). Qed.
Lemma lem394375 {A : Type'} (g : A -> A) (fn : type1423 A) : (term585 A g fn) = (term586 A g fn).
Proof. exact (fun_ext (fun x : A => @lem394374 A g fn x)). Qed.
Lemma lem394376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394377 {A : Type'} (g : A -> A) (fn : type1423 A) : (term587 A g fn) = (term588 A g fn).
Proof. exact (MK_COMB (@lem394376 A) (@lem394375 A g fn)). Qed.
Lemma lem394378 {A : Type'} (g : A -> A) : (term589 A g) = (term590 A g).
Proof. exact (fun_ext (fun fn : type1423 A => @lem394377 A g fn)). Qed.
Lemma lem394379 {A : Type'} : (@ex (A -> nat -> A)) = (@ex (A -> nat -> A)).
Proof. exact (eq_refl (@ex (A -> nat -> A))). Qed.
Lemma lem394380 {A : Type'} (g : A -> A) : (term569 A g) = (term591 A g).
Proof. exact (MK_COMB (@lem394379 A) (@lem394378 A g)). Qed.
Lemma lem394381 {A : Type'} (g : A -> A) : ((term568 A g) = (term569 A g)) = ((term565 A g) = (term591 A g)).
Proof. exact (MK_COMB (@lem394369 A g) (@lem394380 A g)). Qed.
Lemma lem394382 {A : Type'} (g : A -> A) : (term565 A g) = (term591 A g).
Proof. exact (EQ_MP (@lem394381 A g) (@lem394356 A g)). Qed.
Lemma lem394388 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem394338 A P Q) (@lem394337 A P Q)). Qed.
Lemma lem394389 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (@lem394388 A P Q). Qed.
Lemma lem394390 {A : Type'} (g : A -> A) (fn : type1423 A) : (term592 A g fn) = (term593 A g fn).
Proof. exact (@lem394389 A (term594 A fn) (term595 A g fn)). Qed.
Lemma lem394391 {A : Type'} (fn : type1423 A) (x : A) : (term596 A fn x) = ((term597 A fn x) = x).
Proof. exact (eq_refl (term596 A fn x)). Qed.
Lemma lem394392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394393 {A : Type'} (fn : type1423 A) (x : A) : (term598 A fn x) = (term599 A fn x).
Proof. exact (MK_COMB (@lem394392) (@lem394391 A fn x)). Qed.
Lemma lem394394 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term600 A g fn x) = (term601 A g fn x).
Proof. exact (eq_refl (term600 A g fn x)). Qed.
Lemma lem394395 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term602 A g fn x) = (term584 A g fn x).
Proof. exact (MK_COMB (@lem394393 A fn x) (@lem394394 A g fn x)). Qed.
Lemma lem394396 {A : Type'} (g : A -> A) (fn : type1423 A) : (term603 A g fn) = (term586 A g fn).
Proof. exact (fun_ext (fun x : A => @lem394395 A g fn x)). Qed.
Lemma lem394397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394398 {A : Type'} (g : A -> A) (fn : type1423 A) : (term592 A g fn) = (term588 A g fn).
Proof. exact (MK_COMB (@lem394397 A) (@lem394396 A g fn)). Qed.
Lemma lem394399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem394400 {A : Type'} (g : A -> A) (fn : type1423 A) : (term604 A g fn) = (term605 A g fn).
Proof. exact (MK_COMB (@lem394399) (@lem394398 A g fn)). Qed.
Lemma lem394401 {A : Type'} (fn : type1423 A) (x : A) : (term596 A fn x) = ((term597 A fn x) = x).
Proof. exact (eq_refl (term596 A fn x)). Qed.
Lemma lem394402 {A : Type'} (fn : type1423 A) : (term606 A fn) = (term594 A fn).
Proof. exact (fun_ext (fun x : A => @lem394401 A fn x)). Qed.
Lemma lem394403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394404 {A : Type'} (fn : type1423 A) : (term607 A fn) = (term608 A fn).
Proof. exact (MK_COMB (@lem394403 A) (@lem394402 A fn)). Qed.
Lemma lem394405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394406 {A : Type'} (fn : type1423 A) : (term609 A fn) = (term610 A fn).
Proof. exact (MK_COMB (@lem394405) (@lem394404 A fn)). Qed.
Lemma lem394407 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term600 A g fn x) = (term601 A g fn x).
Proof. exact (eq_refl (term600 A g fn x)). Qed.
Lemma lem394408 {A : Type'} (g : A -> A) (fn : type1423 A) : (term611 A g fn) = (term595 A g fn).
Proof. exact (fun_ext (fun x : A => @lem394407 A g fn x)). Qed.
Lemma lem394409 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394410 {A : Type'} (g : A -> A) (fn : type1423 A) : (term612 A g fn) = (term613 A g fn).
Proof. exact (MK_COMB (@lem394409 A) (@lem394408 A g fn)). Qed.
Lemma lem394411 {A : Type'} (g : A -> A) (fn : type1423 A) : (term593 A g fn) = (term614 A g fn).
Proof. exact (MK_COMB (@lem394406 A fn) (@lem394410 A g fn)). Qed.
Lemma lem394412 {A : Type'} (g : A -> A) (fn : type1423 A) : ((term592 A g fn) = (term593 A g fn)) = ((term588 A g fn) = (term614 A g fn)).
Proof. exact (MK_COMB (@lem394400 A g fn) (@lem394411 A g fn)). Qed.
Lemma lem394413 {A : Type'} (g : A -> A) (fn : type1423 A) : (term588 A g fn) = (term614 A g fn).
Proof. exact (EQ_MP (@lem394412 A g fn) (@lem394390 A g fn)). Qed.
Lemma lem394433 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394434 {A : Type'} (f : type1423 A) (y : A) : (term616 A f y) = (f y).
Proof. exact (@lem394433 A (nat -> A) f y). Qed.
Lemma lem394435 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term617 A g fn x n) = (term618 A g fn x n).
Proof. exact (@lem394434 A (term563 A g) (fn x n)). Qed.
Lemma lem394436 {A : Type'} (g : A -> A) (y : A) : (term619 A g y) = (term620 A g y).
Proof. exact (eq_refl (term619 A g y)). Qed.
Lemma lem394437 {A : Type'} (g : A -> A) : (term621 A g) = (term563 A g).
Proof. exact (fun_ext (fun y : A => @lem394436 A g y)). Qed.
Lemma lem394438 {A : Type'} (fn : type1423 A) (x : A) (n : nat) : (fn x n) = (fn x n).
Proof. exact (eq_refl (fn x n)). Qed.
Lemma lem394439 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term617 A g fn x n) = (term618 A g fn x n).
Proof. exact (MK_COMB (@lem394437 A g) (@lem394438 A fn x n)). Qed.
Lemma lem394440 {A : Type'} : (@eq (nat -> A)) = (@eq (nat -> A)).
Proof. exact (eq_refl (@eq (nat -> A))). Qed.
Lemma lem394441 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term622 A g fn x n) = (term623 A g fn x n).
Proof. exact (MK_COMB (@lem394440 A) (@lem394439 A g fn x n)). Qed.
Lemma lem394442 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term618 A g fn x n) = (term624 A g fn x n).
Proof. exact (eq_refl (term618 A g fn x n)). Qed.
Lemma lem394443 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : ((term617 A g fn x n) = (term618 A g fn x n)) = ((term618 A g fn x n) = (term624 A g fn x n)).
Proof. exact (MK_COMB (@lem394441 A g fn x n) (@lem394442 A g fn x n)). Qed.
Lemma lem394444 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term618 A g fn x n) = (term624 A g fn x n).
Proof. exact (EQ_MP (@lem394443 A g fn x n) (@lem394435 A g fn x n)). Qed.
Lemma lem394445 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem394446 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term625 A g fn x n) = (term626 A g fn x n).
Proof. exact (MK_COMB (@lem394444 A g fn x n) (@lem394445 n)). Qed.
Lemma lem394448 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394449 {A : Type'} (f : nat -> A) (y : nat) : (term627 A f y) = (f y).
Proof. exact (@lem394448 nat A f y). Qed.
Lemma lem394450 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term628 A g fn x n) = (term626 A g fn x n).
Proof. exact (@lem394449 A (term624 A g fn x n) n). Qed.
Lemma lem394451 {A : Type'} (n' : nat) (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term629 A g fn x n n') = (term630 A g fn x n).
Proof. exact (eq_refl (term629 A g fn x n n')). Qed.
Lemma lem394452 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term631 A g fn x n) = (term624 A g fn x n).
Proof. exact (fun_ext (fun n' : nat => @lem394451 A n' g fn x n)). Qed.
Lemma lem394453 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem394454 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term628 A g fn x n) = (term626 A g fn x n).
Proof. exact (MK_COMB (@lem394452 A g fn x n) (@lem394453 n)). Qed.
Lemma lem394455 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem394456 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term632 A g fn x n) = (term633 A g fn x n).
Proof. exact (MK_COMB (@lem394455 A) (@lem394454 A g fn x n)). Qed.
Lemma lem394457 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term626 A g fn x n) = (term630 A g fn x n).
Proof. exact (eq_refl (term626 A g fn x n)). Qed.
Lemma lem394458 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : ((term628 A g fn x n) = (term626 A g fn x n)) = ((term626 A g fn x n) = (term630 A g fn x n)).
Proof. exact (MK_COMB (@lem394456 A g fn x n) (@lem394457 A g fn x n)). Qed.
Lemma lem394459 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term626 A g fn x n) = (term630 A g fn x n).
Proof. exact (EQ_MP (@lem394458 A g fn x n) (@lem394450 A g fn x n)). Qed.
Lemma lem394460 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : (term625 A g fn x n) = (term630 A g fn x n).
Proof. exact (TRANS (@lem394446 A g fn x n) (@lem394459 A g fn x n)). Qed.
Lemma lem394461 {A : Type'} (fn : type1423 A) (x : A) (n : nat) : (term634 A fn x n) = (term634 A fn x n).
Proof. exact (eq_refl (term634 A fn x n)). Qed.
Lemma lem394462 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) (n : nat) : ((term635 A fn x n) = (term625 A g fn x n)) = ((term635 A fn x n) = (term630 A g fn x n)).
Proof. exact (MK_COMB (@lem394461 A fn x n) (@lem394460 A g fn x n)). Qed.
Lemma lem394465 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term636 A g fn x) = (term637 A g fn x).
Proof. exact (fun_ext (fun n : nat => @lem394462 A g fn x n)). Qed.
Lemma lem394466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem394467 {A : Type'} (g : A -> A) (fn : type1423 A) (x : A) : (term601 A g fn x) = (term638 A g fn x).
Proof. exact (MK_COMB (@lem394466) (@lem394465 A g fn x)). Qed.
Lemma lem394472 {A : Type'} (g : A -> A) (fn : type1423 A) : (term595 A g fn) = (term639 A g fn).
Proof. exact (fun_ext (fun x : A => @lem394467 A g fn x)). Qed.
Lemma lem394473 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394474 {A : Type'} (g : A -> A) (fn : type1423 A) : (term613 A g fn) = (term640 A g fn).
Proof. exact (MK_COMB (@lem394473 A) (@lem394472 A g fn)). Qed.
Lemma lem394479 {A : Type'} (fn : type1423 A) : (term610 A fn) = (term610 A fn).
Proof. exact (eq_refl (term610 A fn)). Qed.
Lemma lem394480 {A : Type'} (g : A -> A) (fn : type1423 A) : (term614 A g fn) = (term641 A g fn).
Proof. exact (MK_COMB (@lem394479 A fn) (@lem394474 A g fn)). Qed.
Lemma lem394483 {A : Type'} (g : A -> A) (fn : type1423 A) : (term588 A g fn) = (term641 A g fn).
Proof. exact (TRANS (@lem394413 A g fn) (@lem394480 A g fn)). Qed.
Lemma lem394484 {A : Type'} (g : A -> A) : (term590 A g) = (term642 A g).
Proof. exact (fun_ext (fun fn : type1423 A => @lem394483 A g fn)). Qed.
Lemma lem394485 {A : Type'} : (@ex (A -> nat -> A)) = (@ex (A -> nat -> A)).
Proof. exact (eq_refl (@ex (A -> nat -> A))). Qed.
Lemma lem394486 {A : Type'} (g : A -> A) : (term591 A g) = (term643 A g).
Proof. exact (MK_COMB (@lem394485 A) (@lem394484 A g)). Qed.
Lemma lem394491 {A : Type'} (g : A -> A) : (term565 A g) = (term643 A g).
Proof. exact (TRANS (@lem394382 A g) (@lem394486 A g)). Qed.
Lemma lem394492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394493 {A : Type'} (g : A -> A) : (term644 A g) = (term645 A g).
Proof. exact (MK_COMB (@lem394492) (@lem394491 A g)). Qed.
Lemma lem394504 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : (term646 A B P g h) = (term646 A B P g h).
Proof. exact (eq_refl (term646 A B P g h)). Qed.
Lemma lem394505 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : (term647 A B P g h) = (term648 A B P g h).
Proof. exact (MK_COMB (@lem394493 A g) (@lem394504 A B P g h)). Qed.
Lemma lem394508 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : (term648 A B P g h) = (term647 A B P g h).
Proof. exact (SYM (@lem394505 A B P g h)). Qed.
Lemma lem394509 {A : Type'} (g : A -> A) (h1 : term643 A g) : term643 A g.
Proof. exact (h1). Qed.
Lemma lem394510 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term641 A g s) : term641 A g s.
Proof. exact (h1). Qed.
Lemma lem394511 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term640 A g s.
Proof. exact (h1). Qed.
Lemma lem394512 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (h1). Qed.
Lemma lem394513 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term649 A g s.
Proof. exact (h1). Qed.
Lemma lem394515 (P : nat -> Prop) : term242 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem394516 {A : Type'} (g : A -> A) (s : type1423 A) : term650 A g s.
Proof. exact (@lem394515 (term651 A g s)). Qed.
Lemma lem394517 {A : Type'} (g : A -> A) (s : type1423 A) : (term652 A g s) = (term653 A g s).
Proof. exact (eq_refl (term652 A g s)). Qed.
Lemma lem394518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394519 {A : Type'} (g : A -> A) (s : type1423 A) : (term654 A g s) = (term655 A g s).
Proof. exact (MK_COMB (@lem394518) (@lem394517 A g s)). Qed.
Lemma lem394520 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term656 A g s n) = (term657 A g s n).
Proof. exact (eq_refl (term656 A g s n)). Qed.
Lemma lem394521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394522 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term658 A g s n) = (term659 A g s n).
Proof. exact (MK_COMB (@lem394521) (@lem394520 A g s n)). Qed.
Lemma lem394523 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term660 A g s n) = (term661 A g s n).
Proof. exact (eq_refl (term660 A g s n)). Qed.
Lemma lem394524 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term662 A g s n) = (term663 A g s n).
Proof. exact (MK_COMB (@lem394522 A g s n) (@lem394523 A g s n)). Qed.
Lemma lem394525 {A : Type'} (g : A -> A) (s : type1423 A) : (term664 A g s) = (term665 A g s).
Proof. exact (fun_ext (fun n : nat => @lem394524 A g s n)). Qed.
Lemma lem394526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem394527 {A : Type'} (g : A -> A) (s : type1423 A) : (term666 A g s) = (term667 A g s).
Proof. exact (MK_COMB (@lem394526) (@lem394525 A g s)). Qed.
Lemma lem394528 {A : Type'} (g : A -> A) (s : type1423 A) : (term668 A g s) = (term669 A g s).
Proof. exact (MK_COMB (@lem394519 A g s) (@lem394527 A g s)). Qed.
Lemma lem394529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem394530 {A : Type'} (g : A -> A) (s : type1423 A) : (term670 A g s) = (term671 A g s).
Proof. exact (MK_COMB (@lem394529) (@lem394528 A g s)). Qed.
Lemma lem394531 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term656 A g s n) = (term657 A g s n).
Proof. exact (eq_refl (term656 A g s n)). Qed.
Lemma lem394532 {A : Type'} (g : A -> A) (s : type1423 A) : (term672 A g s) = (term651 A g s).
Proof. exact (fun_ext (fun n : nat => @lem394531 A g s n)). Qed.
Lemma lem394533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem394534 {A : Type'} (g : A -> A) (s : type1423 A) : (term673 A g s) = (term649 A g s).
Proof. exact (MK_COMB (@lem394533) (@lem394532 A g s)). Qed.
Lemma lem394535 {A : Type'} (g : A -> A) (s : type1423 A) : (term650 A g s) = (term674 A g s).
Proof. exact (MK_COMB (@lem394530 A g s) (@lem394534 A g s)). Qed.
Lemma lem394536 {A : Type'} (g : A -> A) (s : type1423 A) : term674 A g s.
Proof. exact (EQ_MP (@lem394535 A g s) (@lem394516 A g s)). Qed.
Lemma lem394537 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term657 A g s n) : term657 A g s n.
Proof. exact (h1). Qed.
Lemma lem394538 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term596 A s x.
Proof. exact (@lem394512 A s h1 x). Qed.
Lemma lem394539 {A : Type'} (s : type1423 A) (x : A) : (term596 A s x) = ((term597 A s x) = x).
Proof. exact (eq_refl (term596 A s x)). Qed.
Lemma lem394541 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term675 A g s x.
Proof. exact (@lem394511 A g s h1 x). Qed.
Lemma lem394542 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) : (term675 A g s x) = (term638 A g s x).
Proof. exact (eq_refl (term675 A g s x)). Qed.
Lemma lem394543 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term638 A g s x.
Proof. exact (EQ_MP (@lem394542 A g s x) (@lem394541 A x g s h1)). Qed.
Lemma lem394544 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term676 A g s x n.
Proof. exact (@lem394543 A x g s h1 n). Qed.
Lemma lem394545 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : (term676 A g s x n) = ((term635 A s x n) = (term630 A g s x n)).
Proof. exact (eq_refl (term676 A g s x n)). Qed.
Lemma lem394554 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem394539 A s x) (@lem394538 A x s h1)). Qed.
Lemma lem394555 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem394554 A x s h1). Qed.
Lemma lem394556 {A : Type'} (g : A -> A) (x : A) (s : type1423 A) (h1 : term608 A s) : (term677 A s g x) = (g x).
Proof. exact (@lem394555 A (g x) s h1). Qed.
Lemma lem394557 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem394558 {A : Type'} (g : A -> A) (x : A) (s : type1423 A) (h1 : term608 A s) : (term678 A s g x) = (term679 A g x).
Proof. exact (MK_COMB (@lem394557 A) (@lem394556 A g x s h1)). Qed.
Lemma lem394560 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (EQ_MP (@lem394545 A g s x n) (@lem394544 A x n g s h1)). Qed.
Lemma lem394561 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (@lem394560 A x n g s h1). Qed.
Lemma lem394562 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term680 A s x) = (term681 A g s x).
Proof. exact (@lem394561 A x (NUMERAL 0) g s h1). Qed.
Lemma lem394564 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem394539 A s x) (@lem394538 A x s h1)). Qed.
Lemma lem394565 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem394564 A x s h1). Qed.
Lemma lem394566 {A : Type'} (g : A -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem394567 {A : Type'} (g : A -> A) (x : A) (s : type1423 A) (h1 : term608 A s) : (term681 A g s x) = (g x).
Proof. exact (MK_COMB (@lem394566 A g) (@lem394565 A x s h1)). Qed.
Lemma lem394568 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term680 A s x) = (g x).
Proof. exact (TRANS (@lem394562 A x g s h1) (@lem394567 A g x s h2)). Qed.
Lemma lem394569 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : ((term677 A s g x) = (term680 A s x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem394558 A g x s h2) (@lem394568 A x g s h1 h2)). Qed.
Lemma lem394571 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem394572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem394571 A x). Qed.
Lemma lem394573 {A : Type'} (g : A -> A) (x : A) : ((g x) = (g x)) = True.
Proof. exact (@lem394572 A (g x)). Qed.
Lemma lem394574 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : ((term677 A s g x) = (term680 A s x)) = True.
Proof. exact (TRANS (@lem394569 A x g s h1 h2) (@lem394573 A g x)). Qed.
Lemma lem394575 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term682 A g s) = (term683 A).
Proof. exact (fun_ext (fun x : A => @lem394574 A x g s h1 h2)). Qed.
Lemma lem394576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394577 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term653 A g s) = (term684 A).
Proof. exact (MK_COMB (@lem394576 A) (@lem394575 A g s h1 h2)). Qed.
Lemma lem394579 {A : Type'} (t : Prop) : (term685 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem394580 {A : Type'} (t : Prop) : (term685 A t) = t.
Proof. exact (@lem394579 A t). Qed.
Lemma lem394581 {A : Type'} : (term684 A) = True.
Proof. exact (@lem394580 A True). Qed.
Lemma lem394582 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term653 A g s) = True.
Proof. exact (TRANS (@lem394577 A g s h1 h2) (@lem394581 A)). Qed.
Lemma lem394583 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : True = (term653 A g s).
Proof. exact (SYM (@lem394582 A g s h1 h2)). Qed.
Lemma lem394584 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term653 A g s.
Proof. exact (EQ_MP (@lem394583 A g s h1 h2) (@lem0)). Qed.
Lemma lem394588 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term675 A g s x.
Proof. exact (@lem394511 A g s h1 x). Qed.
Lemma lem394589 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) : (term675 A g s x) = (term638 A g s x).
Proof. exact (eq_refl (term675 A g s x)). Qed.
Lemma lem394590 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term638 A g s x.
Proof. exact (EQ_MP (@lem394589 A g s x) (@lem394588 A x g s h1)). Qed.
Lemma lem394591 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term676 A g s x n.
Proof. exact (@lem394590 A x g s h1 n). Qed.
Lemma lem394592 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : (term676 A g s x n) = ((term635 A s x n) = (term630 A g s x n)).
Proof. exact (eq_refl (term676 A g s x n)). Qed.
Lemma lem394594 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term657 A g s n) : term686 A g s n x.
Proof. exact (@lem394537 A g s n h1 x). Qed.
Lemma lem394595 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : (term686 A g s n x) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl (term686 A g s n x)). Qed.
Lemma lem394604 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (EQ_MP (@lem394592 A g s x n) (@lem394591 A x n g s h1)). Qed.
Lemma lem394605 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (@lem394604 A x n g s h1). Qed.
Lemma lem394606 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term688 A s g x n) = (term689 A s g x n).
Proof. exact (@lem394605 A (g x) n g s h1). Qed.
Lemma lem394608 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term657 A g s n) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394595 A g s x n) (@lem394594 A x g s n h1)). Qed.
Lemma lem394609 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term657 A g s n) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394608 A x g s n h1). Qed.
Lemma lem394611 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (EQ_MP (@lem394592 A g s x n) (@lem394591 A x n g s h1)). Qed.
Lemma lem394612 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (@lem394611 A x n g s h1). Qed.
Lemma lem394613 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term687 A s g x n) = (term630 A g s x n).
Proof. exact (TRANS (@lem394609 A x g s n h2) (@lem394612 A x n g s h1)). Qed.
Lemma lem394614 {A : Type'} (g : A -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem394615 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term689 A s g x n) = (term690 A g s x n).
Proof. exact (MK_COMB (@lem394614 A g) (@lem394613 A x g s n h1 h2)). Qed.
Lemma lem394616 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term688 A s g x n) = (term690 A g s x n).
Proof. exact (TRANS (@lem394606 A x n g s h1) (@lem394615 A x g s n h1 h2)). Qed.
Lemma lem394617 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem394618 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term691 A s g x n) = (term692 A g s x n).
Proof. exact (MK_COMB (@lem394617 A) (@lem394616 A x g s n h1 h2)). Qed.
Lemma lem394620 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (EQ_MP (@lem394592 A g s x n) (@lem394591 A x n g s h1)). Qed.
Lemma lem394621 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (@lem394620 A x n g s h1). Qed.
Lemma lem394622 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term693 A s x n) = (term694 A g s x n).
Proof. exact (@lem394621 A x (S n) g s h1). Qed.
Lemma lem394624 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (EQ_MP (@lem394592 A g s x n) (@lem394591 A x n g s h1)). Qed.
Lemma lem394625 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term635 A s x n) = (term630 A g s x n).
Proof. exact (@lem394624 A x n g s h1). Qed.
Lemma lem394626 {A : Type'} (g : A -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem394627 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term694 A g s x n) = (term690 A g s x n).
Proof. exact (MK_COMB (@lem394626 A g) (@lem394625 A x n g s h1)). Qed.
Lemma lem394628 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : (term693 A s x n) = (term690 A g s x n).
Proof. exact (TRANS (@lem394622 A x n g s h1) (@lem394627 A x n g s h1)). Qed.
Lemma lem394629 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : ((term688 A s g x n) = (term693 A s x n)) = ((term690 A g s x n) = (term690 A g s x n)).
Proof. exact (MK_COMB (@lem394618 A x g s n h1 h2) (@lem394628 A x n g s h1)). Qed.
Lemma lem394631 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem394632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem394631 A x). Qed.
Lemma lem394633 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : ((term690 A g s x n) = (term690 A g s x n)) = True.
Proof. exact (@lem394632 A (term690 A g s x n)). Qed.
Lemma lem394634 {A : Type'} (x : A) (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : ((term688 A s g x n) = (term693 A s x n)) = True.
Proof. exact (TRANS (@lem394629 A x g s n h1 h2) (@lem394633 A g s x n)). Qed.
Lemma lem394635 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term695 A g s n) = (term683 A).
Proof. exact (fun_ext (fun x : A => @lem394634 A x g s n h1 h2)). Qed.
Lemma lem394636 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem394637 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term661 A g s n) = (term684 A).
Proof. exact (MK_COMB (@lem394636 A) (@lem394635 A g s n h1 h2)). Qed.
Lemma lem394639 {A : Type'} (t : Prop) : (term685 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem394640 {A : Type'} (t : Prop) : (term685 A t) = t.
Proof. exact (@lem394639 A t). Qed.
Lemma lem394641 {A : Type'} : (term684 A) = True.
Proof. exact (@lem394640 A True). Qed.
Lemma lem394642 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : (term661 A g s n) = True.
Proof. exact (TRANS (@lem394637 A g s n h1 h2) (@lem394641 A)). Qed.
Lemma lem394643 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : True = (term661 A g s n).
Proof. exact (SYM (@lem394642 A g s n h1 h2)). Qed.
Lemma lem394644 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) (h1 : term640 A g s) (h2 : term657 A g s n) : term661 A g s n.
Proof. exact (EQ_MP (@lem394643 A g s n h1 h2) (@lem0)). Qed.
Lemma lem394645 {A : Type'} (n : nat) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term663 A g s n.
Proof. exact (fun h0 : term657 A g s n => @lem394644 A g s n h1 h0). Qed.
Lemma lem394650 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) : term667 A g s.
Proof. exact (fun n : nat => @lem394645 A n g s h1). Qed.
Lemma lem394651 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term669 A g s.
Proof. exact (conj (@lem394584 A g s h1 h2) (@lem394650 A g s h1)). Qed.
Lemma lem394652 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term649 A g s.
Proof. exact (@lem394536 A g s (@lem394651 A g s h1 h2)). Qed.
Lemma lem394656 {A : Type'} (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term656 A g s n.
Proof. exact (@lem394513 A g s h1 n). Qed.
Lemma lem394657 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term656 A g s n) = (term657 A g s n).
Proof. exact (eq_refl (term656 A g s n)). Qed.
Lemma lem394658 {A : Type'} (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term657 A g s n.
Proof. exact (EQ_MP (@lem394657 A g s n) (@lem394656 A n g s h1)). Qed.
Lemma lem394659 {A : Type'} (n : nat) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term686 A g s n x.
Proof. exact (@lem394658 A n g s h1 x). Qed.
Lemma lem394660 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : (term686 A g s n x) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl (term686 A g s n x)). Qed.
Lemma lem394662 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem394667 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394668 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (@lem394667 A B f y). Qed.
Lemma lem394669 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x).
Proof. exact (@lem394668 A B (term698 A B h P s something_arbitrary) x). Qed.
Lemma lem394670 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394671 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) : (term700 A B h P s something_arbitrary) = (term698 A B h P s something_arbitrary).
Proof. exact (fun_ext (fun x : A => @lem394670 A B h P s x something_arbitrary)). Qed.
Lemma lem394672 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem394673 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x).
Proof. exact (MK_COMB (@lem394671 A B h P s something_arbitrary) (@lem394672 A x)). Qed.
Lemma lem394674 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394675 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term701 A B h P s something_arbitrary x) = (term702 A B h P s something_arbitrary x).
Proof. exact (MK_COMB (@lem394674 B) (@lem394673 A B h P s something_arbitrary x)). Qed.
Lemma lem394676 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394677 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x)) = ((term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary)).
Proof. exact (MK_COMB (@lem394675 A B h P s something_arbitrary x) (@lem394676 A B h P s x something_arbitrary)). Qed.
Lemma lem394678 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem394677 A B h P s x something_arbitrary) (@lem394669 A B h P s something_arbitrary x)). Qed.
Lemma lem394699 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394700 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term702 A B h P s something_arbitrary x) = (term703 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394699 B) (@lem394678 A B h P s x something_arbitrary)). Qed.
Lemma lem394702 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem394662 A P x) (@lem394332 A P x h1)). Qed.
Lemma lem394703 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem394704 {A B : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (term704 A B P x) = (@COND B True).
Proof. exact (MK_COMB (@lem394703 B) (@lem394702 A P x h1)). Qed.
Lemma lem394706 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394707 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (@lem394706 A B f y). Qed.
Lemma lem394708 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x).
Proof. exact (@lem394707 A B (term698 A B h P s something_arbitrary) (g x)). Qed.
Lemma lem394709 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394710 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) : (term700 A B h P s something_arbitrary) = (term698 A B h P s something_arbitrary).
Proof. exact (fun_ext (fun x : A => @lem394709 A B h P s x something_arbitrary)). Qed.
Lemma lem394711 {A : Type'} (g : A -> A) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem394712 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x).
Proof. exact (MK_COMB (@lem394710 A B h P s something_arbitrary) (@lem394711 A g x)). Qed.
Lemma lem394713 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394714 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term707 A B h P s something_arbitrary g x) = (term708 A B h P s something_arbitrary g x).
Proof. exact (MK_COMB (@lem394713 B) (@lem394712 A B h P s something_arbitrary g x)). Qed.
Lemma lem394715 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : (term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary).
Proof. exact (eq_refl (term706 A B h P s something_arbitrary g x)). Qed.
Lemma lem394716 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : ((term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x)) = ((term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary)).
Proof. exact (MK_COMB (@lem394714 A B h P s something_arbitrary g x) (@lem394715 A B h P s g x something_arbitrary)). Qed.
Lemma lem394717 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : (term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary).
Proof. exact (EQ_MP (@lem394716 A B h P s g x something_arbitrary) (@lem394708 A B h P s something_arbitrary g x)). Qed.
Lemma lem394723 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394660 A g s x n) (@lem394659 A n x g s h1)). Qed.
Lemma lem394724 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394723 A x n g s h1). Qed.
Lemma lem394725 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394726 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x n) = (term711 A P s x n).
Proof. exact (MK_COMB (@lem394725 A P) (@lem394724 A x n g s h1)). Qed.
Lemma lem394727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem394728 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term712 A P s g x n) = (term713 A P s x n).
Proof. exact (MK_COMB (@lem394727) (@lem394726 A P x n g s h1)). Qed.
Lemma lem394729 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term714 A P s g x) = (term715 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem394728 A P x n g s h1)). Qed.
Lemma lem394730 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem394731 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term716 A P s g x) = (term717 A P s x).
Proof. exact (MK_COMB (@lem394730) (@lem394729 A P x g s h1)). Qed.
Lemma lem394736 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem394737 {A B : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term718 A B P s g x) = (term719 A B P s x).
Proof. exact (MK_COMB (@lem394736 B) (@lem394731 A P x g s h1)). Qed.
Lemma lem394747 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394660 A g s x n) (@lem394659 A n x g s h1)). Qed.
Lemma lem394748 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394747 A x n g s h1). Qed.
Lemma lem394749 {A : Type'} (y : A) : (@eq A y) = (@eq A y).
Proof. exact (eq_refl (@eq A y)). Qed.
Lemma lem394750 {A : Type'} (y : A) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (y = (term687 A s g x n)) = (y = (term635 A s x n)).
Proof. exact (MK_COMB (@lem394749 A y) (@lem394748 A x n g s h1)). Qed.
Lemma lem394753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394754 {A : Type'} (y : A) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term720 A y s g x n) = (term721 A y s x n).
Proof. exact (MK_COMB (@lem394753) (@lem394750 A y x n g s h1)). Qed.
Lemma lem394758 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394660 A g s x n) (@lem394659 A n x g s h1)). Qed.
Lemma lem394759 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394758 A x n g s h1). Qed.
Lemma lem394760 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394761 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x n) = (term711 A P s x n).
Proof. exact (MK_COMB (@lem394760 A P) (@lem394759 A x n g s h1)). Qed.
Lemma lem394762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem394763 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term712 A P s g x n) = (term713 A P s x n).
Proof. exact (MK_COMB (@lem394762) (@lem394761 A P x n g s h1)). Qed.
Lemma lem394764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394765 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term722 A P s g x n) = (term723 A P s x n).
Proof. exact (MK_COMB (@lem394764) (@lem394763 A P x n g s h1)). Qed.
Lemma lem394773 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394660 A g s x n) (@lem394659 A n x g s h1)). Qed.
Lemma lem394774 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394773 A x n g s h1). Qed.
Lemma lem394775 {A : Type'} (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x m) = (term635 A s x m).
Proof. exact (@lem394774 A x m g s h1). Qed.
Lemma lem394776 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394777 {A : Type'} (P : A -> Prop) (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x m) = (term711 A P s x m).
Proof. exact (MK_COMB (@lem394776 A P) (@lem394775 A x m g s h1)). Qed.
Lemma lem394778 (m : nat) (n : nat) : (term438 m n) = (term438 m n).
Proof. exact (eq_refl (term438 m n)). Qed.
Lemma lem394779 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term724 A n P s g x m) = (term725 A n P s x m).
Proof. exact (MK_COMB (@lem394778 m n) (@lem394777 A P x m g s h1)). Qed.
Lemma lem394782 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term726 A n P s g x) = (term727 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem394779 A n P x m g s h1)). Qed.
Lemma lem394783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem394784 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term728 A n P s g x) = (term729 A n P s x).
Proof. exact (MK_COMB (@lem394783) (@lem394782 A n P x g s h1)). Qed.
Lemma lem394789 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term730 A n P s g x) = (term731 A n P s x).
Proof. exact (MK_COMB (@lem394765 A P x n g s h1) (@lem394784 A n P x g s h1)). Qed.
Lemma lem394792 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term732 A y n P s g x) = (term733 A y n P s x).
Proof. exact (MK_COMB (@lem394754 A y x n g s h1) (@lem394789 A n P x g s h1)). Qed.
Lemma lem394795 {A : Type'} (y : A) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term734 A y P s g x) = (term735 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem394792 A y n P x g s h1)). Qed.
Lemma lem394796 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem394797 {A : Type'} (y : A) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term736 A y P s g x) = (term737 A y P s x).
Proof. exact (MK_COMB (@lem394796) (@lem394795 A y P x g s h1)). Qed.
Lemma lem394802 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term738 A P s g x) = (term739 A P s x).
Proof. exact (fun_ext (fun y : A => @lem394797 A y P x g s h1)). Qed.
Lemma lem394803 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem394804 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term740 A P s g x) = (term741 A P s x).
Proof. exact (MK_COMB (@lem394803 A) (@lem394802 A P x g s h1)). Qed.
Lemma lem394805 {A B : Type'} (h : A -> B) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem394806 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term742 A B h P s g x) = (term743 A B h P s x).
Proof. exact (MK_COMB (@lem394805 A B h) (@lem394804 A P x g s h1)). Qed.
Lemma lem394807 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term744 A B h P s g x) = (term745 A B h P s x).
Proof. exact (MK_COMB (@lem394737 A B P x g s h1) (@lem394806 A B h P x g s h1)). Qed.
Lemma lem394808 {B : Type'} (something_arbitrary : B) : something_arbitrary = something_arbitrary.
Proof. exact (eq_refl something_arbitrary). Qed.
Lemma lem394809 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term709 A B h P s g x something_arbitrary) = (term746 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394807 A B h P x g s h1) (@lem394808 B something_arbitrary)). Qed.
Lemma lem394810 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term706 A B h P s something_arbitrary g x) = (term746 A B h P s x something_arbitrary).
Proof. exact (TRANS (@lem394717 A B h P s g x something_arbitrary) (@lem394809 A B h P x something_arbitrary g s h1)). Qed.
Lemma lem394811 {A B : Type'} (h : A -> B) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : P x) : (term747 A B h P s something_arbitrary g x) = (term748 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394704 A B P x h2) (@lem394810 A B h P x something_arbitrary g s h1)). Qed.
Lemma lem394812 {A B : Type'} (h : A -> B) (x : A) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem394813 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : P x) : (term749 A B P s something_arbitrary g h x) = (term750 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem394811 A B h something_arbitrary g s P x h1 h2) (@lem394812 A B h x)). Qed.
Lemma lem394815 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem394816 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem394815 B t2 t1). Qed.
Lemma lem394817 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term750 A B P s something_arbitrary h x) = (term746 A B h P s x something_arbitrary).
Proof. exact (@lem394816 B (h x) (term746 A B h P s x something_arbitrary)). Qed.
Lemma lem394838 {A B : Type'} (h : A -> B) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : P x) : (term749 A B P s something_arbitrary g h x) = (term746 A B h P s x something_arbitrary).
Proof. exact (TRANS (@lem394813 A B something_arbitrary h g s P x h1 h2) (@lem394817 A B h P s x something_arbitrary)). Qed.
Lemma lem394839 {A B : Type'} (h : A -> B) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : P x) : ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)) = ((term699 A B h P s x something_arbitrary) = (term746 A B h P s x something_arbitrary)).
Proof. exact (MK_COMB (@lem394700 A B h P s x something_arbitrary) (@lem394838 A B h something_arbitrary g s P x h1 h2)). Qed.
Lemma lem394842 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : P x) : ((term699 A B h P s x something_arbitrary) = (term746 A B h P s x something_arbitrary)) = ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)).
Proof. exact (SYM (@lem394839 A B h something_arbitrary g s P x h1 h2)). Qed.
Lemma lem394846 {A : Type'} (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term656 A g s n.
Proof. exact (@lem394513 A g s h1 n). Qed.
Lemma lem394847 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term656 A g s n) = (term657 A g s n).
Proof. exact (eq_refl (term656 A g s n)). Qed.
Lemma lem394848 {A : Type'} (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term657 A g s n.
Proof. exact (EQ_MP (@lem394847 A g s n) (@lem394846 A n g s h1)). Qed.
Lemma lem394849 {A : Type'} (n : nat) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : term686 A g s n x.
Proof. exact (@lem394848 A n g s h1 x). Qed.
Lemma lem394850 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : (term686 A g s n x) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl (term686 A g s n x)). Qed.
Lemma lem394852 {A : Type'} (P : A -> Prop) (x : A) : term751 A P x.
Proof. exact (@lem82 (P x)). Qed.
Lemma lem394857 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394858 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (@lem394857 A B f y). Qed.
Lemma lem394859 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x).
Proof. exact (@lem394858 A B (term698 A B h P s something_arbitrary) x). Qed.
Lemma lem394860 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394861 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) : (term700 A B h P s something_arbitrary) = (term698 A B h P s something_arbitrary).
Proof. exact (fun_ext (fun x : A => @lem394860 A B h P s x something_arbitrary)). Qed.
Lemma lem394862 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem394863 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x).
Proof. exact (MK_COMB (@lem394861 A B h P s something_arbitrary) (@lem394862 A x)). Qed.
Lemma lem394864 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394865 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (x : A) : (term701 A B h P s something_arbitrary x) = (term702 A B h P s something_arbitrary x).
Proof. exact (MK_COMB (@lem394864 B) (@lem394863 A B h P s something_arbitrary x)). Qed.
Lemma lem394866 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394867 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term696 A B h P s something_arbitrary x) = (term697 A B h P s something_arbitrary x)) = ((term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary)).
Proof. exact (MK_COMB (@lem394865 A B h P s something_arbitrary x) (@lem394866 A B h P s x something_arbitrary)). Qed.
Lemma lem394868 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem394867 A B h P s x something_arbitrary) (@lem394859 A B h P s something_arbitrary x)). Qed.
Lemma lem394889 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394890 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term702 A B h P s something_arbitrary x) = (term703 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394889 B) (@lem394868 A B h P s x something_arbitrary)). Qed.
Lemma lem394892 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : (P x) = False.
Proof. exact (@lem394852 A P x (@lem394333 A P x h1)). Qed.
Lemma lem394893 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem394894 {A B : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : (term704 A B P x) = (@COND B False).
Proof. exact (MK_COMB (@lem394893 B) (@lem394892 A P x h1)). Qed.
Lemma lem394896 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem394897 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (@lem394896 A B f y). Qed.
Lemma lem394898 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x).
Proof. exact (@lem394897 A B (term698 A B h P s something_arbitrary) (g x)). Qed.
Lemma lem394899 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term697 A B h P s something_arbitrary x) = (term699 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term697 A B h P s something_arbitrary x)). Qed.
Lemma lem394900 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) : (term700 A B h P s something_arbitrary) = (term698 A B h P s something_arbitrary).
Proof. exact (fun_ext (fun x : A => @lem394899 A B h P s x something_arbitrary)). Qed.
Lemma lem394901 {A : Type'} (g : A -> A) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem394902 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x).
Proof. exact (MK_COMB (@lem394900 A B h P s something_arbitrary) (@lem394901 A g x)). Qed.
Lemma lem394903 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem394904 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (g : A -> A) (x : A) : (term707 A B h P s something_arbitrary g x) = (term708 A B h P s something_arbitrary g x).
Proof. exact (MK_COMB (@lem394903 B) (@lem394902 A B h P s something_arbitrary g x)). Qed.
Lemma lem394905 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : (term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary).
Proof. exact (eq_refl (term706 A B h P s something_arbitrary g x)). Qed.
Lemma lem394906 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : ((term705 A B h P s something_arbitrary g x) = (term706 A B h P s something_arbitrary g x)) = ((term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary)).
Proof. exact (MK_COMB (@lem394904 A B h P s something_arbitrary g x) (@lem394905 A B h P s g x something_arbitrary)). Qed.
Lemma lem394907 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (g : A -> A) (x : A) (something_arbitrary : B) : (term706 A B h P s something_arbitrary g x) = (term709 A B h P s g x something_arbitrary).
Proof. exact (EQ_MP (@lem394906 A B h P s g x something_arbitrary) (@lem394898 A B h P s something_arbitrary g x)). Qed.
Lemma lem394913 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394850 A g s x n) (@lem394849 A n x g s h1)). Qed.
Lemma lem394914 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394913 A x n g s h1). Qed.
Lemma lem394915 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394916 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x n) = (term711 A P s x n).
Proof. exact (MK_COMB (@lem394915 A P) (@lem394914 A x n g s h1)). Qed.
Lemma lem394917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem394918 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term712 A P s g x n) = (term713 A P s x n).
Proof. exact (MK_COMB (@lem394917) (@lem394916 A P x n g s h1)). Qed.
Lemma lem394919 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term714 A P s g x) = (term715 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem394918 A P x n g s h1)). Qed.
Lemma lem394920 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem394921 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term716 A P s g x) = (term717 A P s x).
Proof. exact (MK_COMB (@lem394920) (@lem394919 A P x g s h1)). Qed.
Lemma lem394926 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem394927 {A B : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term718 A B P s g x) = (term719 A B P s x).
Proof. exact (MK_COMB (@lem394926 B) (@lem394921 A P x g s h1)). Qed.
Lemma lem394937 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394850 A g s x n) (@lem394849 A n x g s h1)). Qed.
Lemma lem394938 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394937 A x n g s h1). Qed.
Lemma lem394939 {A : Type'} (y : A) : (@eq A y) = (@eq A y).
Proof. exact (eq_refl (@eq A y)). Qed.
Lemma lem394940 {A : Type'} (y : A) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (y = (term687 A s g x n)) = (y = (term635 A s x n)).
Proof. exact (MK_COMB (@lem394939 A y) (@lem394938 A x n g s h1)). Qed.
Lemma lem394943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394944 {A : Type'} (y : A) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term720 A y s g x n) = (term721 A y s x n).
Proof. exact (MK_COMB (@lem394943) (@lem394940 A y x n g s h1)). Qed.
Lemma lem394948 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394850 A g s x n) (@lem394849 A n x g s h1)). Qed.
Lemma lem394949 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394948 A x n g s h1). Qed.
Lemma lem394950 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394951 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x n) = (term711 A P s x n).
Proof. exact (MK_COMB (@lem394950 A P) (@lem394949 A x n g s h1)). Qed.
Lemma lem394952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem394953 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term712 A P s g x n) = (term713 A P s x n).
Proof. exact (MK_COMB (@lem394952) (@lem394951 A P x n g s h1)). Qed.
Lemma lem394954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem394955 {A : Type'} (P : A -> Prop) (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term722 A P s g x n) = (term723 A P s x n).
Proof. exact (MK_COMB (@lem394954) (@lem394953 A P x n g s h1)). Qed.
Lemma lem394963 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (EQ_MP (@lem394850 A g s x n) (@lem394849 A n x g s h1)). Qed.
Lemma lem394964 {A : Type'} (x : A) (n : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x n) = (term635 A s x n).
Proof. exact (@lem394963 A x n g s h1). Qed.
Lemma lem394965 {A : Type'} (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term687 A s g x m) = (term635 A s x m).
Proof. exact (@lem394964 A x m g s h1). Qed.
Lemma lem394966 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem394967 {A : Type'} (P : A -> Prop) (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term710 A P s g x m) = (term711 A P s x m).
Proof. exact (MK_COMB (@lem394966 A P) (@lem394965 A x m g s h1)). Qed.
Lemma lem394968 (m : nat) (n : nat) : (term438 m n) = (term438 m n).
Proof. exact (eq_refl (term438 m n)). Qed.
Lemma lem394969 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (m : nat) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term724 A n P s g x m) = (term725 A n P s x m).
Proof. exact (MK_COMB (@lem394968 m n) (@lem394967 A P x m g s h1)). Qed.
Lemma lem394972 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term726 A n P s g x) = (term727 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem394969 A n P x m g s h1)). Qed.
Lemma lem394973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem394974 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term728 A n P s g x) = (term729 A n P s x).
Proof. exact (MK_COMB (@lem394973) (@lem394972 A n P x g s h1)). Qed.
Lemma lem394979 {A : Type'} (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term730 A n P s g x) = (term731 A n P s x).
Proof. exact (MK_COMB (@lem394955 A P x n g s h1) (@lem394974 A n P x g s h1)). Qed.
Lemma lem394982 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term732 A y n P s g x) = (term733 A y n P s x).
Proof. exact (MK_COMB (@lem394944 A y x n g s h1) (@lem394979 A n P x g s h1)). Qed.
Lemma lem394985 {A : Type'} (y : A) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term734 A y P s g x) = (term735 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem394982 A y n P x g s h1)). Qed.
Lemma lem394986 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem394987 {A : Type'} (y : A) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term736 A y P s g x) = (term737 A y P s x).
Proof. exact (MK_COMB (@lem394986) (@lem394985 A y P x g s h1)). Qed.
Lemma lem394992 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term738 A P s g x) = (term739 A P s x).
Proof. exact (fun_ext (fun y : A => @lem394987 A y P x g s h1)). Qed.
Lemma lem394993 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem394994 {A : Type'} (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term740 A P s g x) = (term741 A P s x).
Proof. exact (MK_COMB (@lem394993 A) (@lem394992 A P x g s h1)). Qed.
Lemma lem394995 {A B : Type'} (h : A -> B) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem394996 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term742 A B h P s g x) = (term743 A B h P s x).
Proof. exact (MK_COMB (@lem394995 A B h) (@lem394994 A P x g s h1)). Qed.
Lemma lem394997 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term744 A B h P s g x) = (term745 A B h P s x).
Proof. exact (MK_COMB (@lem394927 A B P x g s h1) (@lem394996 A B h P x g s h1)). Qed.
Lemma lem394998 {B : Type'} (something_arbitrary : B) : something_arbitrary = something_arbitrary.
Proof. exact (eq_refl something_arbitrary). Qed.
Lemma lem394999 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term709 A B h P s g x something_arbitrary) = (term746 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394997 A B h P x g s h1) (@lem394998 B something_arbitrary)). Qed.
Lemma lem395000 {A B : Type'} (h : A -> B) (P : A -> Prop) (x : A) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (h1 : term649 A g s) : (term706 A B h P s something_arbitrary g x) = (term746 A B h P s x something_arbitrary).
Proof. exact (TRANS (@lem394907 A B h P s g x something_arbitrary) (@lem394999 A B h P x something_arbitrary g s h1)). Qed.
Lemma lem395001 {A B : Type'} (h : A -> B) (something_arbitrary : B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : term554 A P x) : (term747 A B h P s something_arbitrary g x) = (term752 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem394894 A B P x h2) (@lem395000 A B h P x something_arbitrary g s h1)). Qed.
Lemma lem395002 {A B : Type'} (h : A -> B) (x : A) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem395003 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : term554 A P x) : (term749 A B P s something_arbitrary g h x) = (term753 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem395001 A B h something_arbitrary g s P x h1 h2) (@lem395002 A B h x)). Qed.
Lemma lem395005 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem395006 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem395005 B t1 t2). Qed.
Lemma lem395007 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term753 A B P s something_arbitrary h x) = (h x).
Proof. exact (@lem395006 B (term746 A B h P s x something_arbitrary) (h x)). Qed.
Lemma lem395008 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : term554 A P x) : (term749 A B P s something_arbitrary g h x) = (h x).
Proof. exact (TRANS (@lem395003 A B something_arbitrary h g s P x h1 h2) (@lem395007 A B P s something_arbitrary h x)). Qed.
Lemma lem395009 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : term554 A P x) : ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)) = ((term699 A B h P s x something_arbitrary) = (h x)).
Proof. exact (MK_COMB (@lem394890 A B h P s x something_arbitrary) (@lem395008 A B something_arbitrary h g s P x h1 h2)). Qed.
Lemma lem395012 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term649 A g s) (h2 : term554 A P x) : ((term699 A B h P s x something_arbitrary) = (h x)) = ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)).
Proof. exact (SYM (@lem395009 A B something_arbitrary h g s P x h1 h2)). Qed.
Lemma lem395013 (P : nat -> Prop) (h1 : term67 P) : term67 P.
Proof. exact (h1). Qed.
Lemma lem395014 (P : nat -> Prop) (h1 : term67 P) : (term32 P) = (term29 P).
Proof. exact (@lem389869 P (@lem395013 P h1)). Qed.
Lemma lem395020 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term596 A s x.
Proof. exact (@lem394512 A s h1 x). Qed.
Lemma lem395021 {A : Type'} (s : type1423 A) (x : A) : (term596 A s x) = ((term597 A s x) = x).
Proof. exact (eq_refl (term596 A s x)). Qed.
Lemma lem395029 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem395233 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term754 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem395234 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term755 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem395233 _2963 g t e g' t' e'). Qed.
Lemma lem395235 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term756 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem395234 _2963 g t e g' t'). Qed.
Lemma lem395236 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term757 _2963 g t e.
Proof. exact (fun g' : Prop => @lem395235 _2963 g t e g'). Qed.
Lemma lem395237 {B : Type'} (g : Prop) (t : B) (e : B) : term757 B g t e.
Proof. exact (@lem395236 B g t e). Qed.
Lemma lem395238 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : term758 A B h P s x something_arbitrary.
Proof. exact (@lem395237 B (term717 A P s x) (term743 A B h P s x) something_arbitrary). Qed.
Lemma lem395239 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) : term759 A B h P s x something_arbitrary g'.
Proof. exact (@lem395238 A B h P s x something_arbitrary g'). Qed.
Lemma lem395240 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) : (term759 A B h P s x something_arbitrary g') = (term760 A B h P s x something_arbitrary g').
Proof. exact (eq_refl (term759 A B h P s x something_arbitrary g')). Qed.
Lemma lem395241 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) : term760 A B h P s x something_arbitrary g'.
Proof. exact (EQ_MP (@lem395240 A B h P s x something_arbitrary g') (@lem395239 A B h P s x something_arbitrary g')). Qed.
Lemma lem395242 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) : term761 A B h P s x something_arbitrary g' t'.
Proof. exact (@lem395241 A B h P s x something_arbitrary g' t'). Qed.
Lemma lem395243 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) : (term761 A B h P s x something_arbitrary g' t') = (term762 A B h P s x something_arbitrary g' t').
Proof. exact (eq_refl (term761 A B h P s x something_arbitrary g' t')). Qed.
Lemma lem395244 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) : term762 A B h P s x something_arbitrary g' t'.
Proof. exact (EQ_MP (@lem395243 A B h P s x something_arbitrary g' t') (@lem395242 A B h P s x something_arbitrary g' t')). Qed.
Lemma lem395245 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) (e' : B) : term763 A B h P s x something_arbitrary g' t' e'.
Proof. exact (@lem395244 A B h P s x something_arbitrary g' t' e'). Qed.
Lemma lem395246 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) (e' : B) : (term763 A B h P s x something_arbitrary g' t' e') = (term764 A B h P s x something_arbitrary g' t' e').
Proof. exact (eq_refl (term763 A B h P s x something_arbitrary g' t' e')). Qed.
Lemma lem395247 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (g' : Prop) (t' : B) (e' : B) : term764 A B h P s x something_arbitrary g' t' e'.
Proof. exact (EQ_MP (@lem395246 A B h P s x something_arbitrary g' t' e') (@lem395245 A B h P s x something_arbitrary g' t' e')). Qed.
Lemma lem395253 (P : nat -> Prop) : term1 P.
Proof. exact (fun h0 : term67 P => @lem395014 P h0). Qed.
Lemma lem395254 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term765 A P s x.
Proof. exact (@lem395253 (term766 A P s x)). Qed.
Lemma lem395255 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term767 A P s x) = (term768 A P s x).
Proof. exact (eq_refl (term767 A P s x)). Qed.
Lemma lem395256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem395257 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term769 A P s x) = (term770 A P s x).
Proof. exact (MK_COMB (@lem395256) (@lem395255 A P s x)). Qed.
Lemma lem395258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem395259 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term771 A P s x) = (term772 A P s x).
Proof. exact (MK_COMB (@lem395258) (@lem395257 A P s x)). Qed.
Lemma lem395260 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term773 A P s x n) = (term713 A P s x n).
Proof. exact (eq_refl (term773 A P s x n)). Qed.
Lemma lem395261 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term774 A P s x) = (term715 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem395260 A P s x n)). Qed.
Lemma lem395262 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem395263 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term775 A P s x) = (term717 A P s x).
Proof. exact (MK_COMB (@lem395262) (@lem395261 A P s x)). Qed.
Lemma lem395264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem395265 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term776 A P s x) = (term777 A P s x).
Proof. exact (MK_COMB (@lem395264) (@lem395263 A P s x)). Qed.
Lemma lem395266 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term778 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term778 A P s x n)). Qed.
Lemma lem395267 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term780 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem395266 A P s x n)). Qed.
Lemma lem395268 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem395269 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term781 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem395268) (@lem395267 A P s x)). Qed.
Lemma lem395270 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : ((term775 A P s x) = (term781 A P s x)) = ((term717 A P s x) = (term782 A P s x)).
Proof. exact (MK_COMB (@lem395265 A P s x) (@lem395269 A P s x)). Qed.
Lemma lem395271 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term765 A P s x) = (term783 A P s x).
Proof. exact (MK_COMB (@lem395259 A P s x) (@lem395270 A P s x)). Qed.
Lemma lem395272 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term783 A P s x.
Proof. exact (EQ_MP (@lem395271 A P s x) (@lem395254 A P s x)). Qed.
Lemma lem395274 (t : Prop) : (term198 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem395275 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term770 A P s x) = (term784 A P s x).
Proof. exact (@lem395274 (term784 A P s x)). Qed.
Lemma lem395277 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem395021 A s x) (@lem395020 A x s h1)). Qed.
Lemma lem395278 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem395277 A x s h1). Qed.
Lemma lem395279 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem395280 {A : Type'} (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : (term784 A P s x) = (P x).
Proof. exact (MK_COMB (@lem395279 A P) (@lem395278 A x s h1)). Qed.
Lemma lem395282 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem395029 A P x) (@lem394332 A P x h1)). Qed.
Lemma lem395283 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term784 A P s x) = True.
Proof. exact (TRANS (@lem395280 A P x s h1) (@lem395282 A P x h2)). Qed.
Lemma lem395284 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term770 A P s x) = True.
Proof. exact (TRANS (@lem395275 A P s x) (@lem395283 A s P x h1 h2)). Qed.
Lemma lem395285 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : True = (term770 A P s x).
Proof. exact (SYM (@lem395284 A s P x h1 h2)). Qed.
Lemma lem395286 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term770 A P s x.
Proof. exact (EQ_MP (@lem395285 A s P x h1 h2) (@lem0)). Qed.
Lemma lem395287 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term717 A P s x) = (term782 A P s x).
Proof. exact (@lem395272 A P s x (@lem395286 A s P x h1 h2)). Qed.
Lemma lem395313 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (t' : B) (e' : B) : term785 A B h something_arbitrary P s x t' e'.
Proof. exact (@lem395247 A B h P s x something_arbitrary (term782 A P s x) t' e'). Qed.
Lemma lem395314 {A B : Type'} (h : A -> B) (something_arbitrary : B) (t' : B) (e' : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term786 A B h something_arbitrary P s x t' e'.
Proof. exact (@lem395313 A B h something_arbitrary P s x t' e' (@lem395287 A s P x h1 h2)). Qed.
Lemma lem395376 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : (term743 A B h P s x) = (term743 A B h P s x).
Proof. exact (eq_refl (term743 A B h P s x)). Qed.
Lemma lem395377 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : term787 A B h P s x.
Proof. exact (fun h0 : term782 A P s x => @lem395376 A B h P s x). Qed.
Lemma lem395378 {A B : Type'} (something_arbitrary : B) (h : A -> B) (e' : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term788 A B something_arbitrary h P s x e'.
Proof. exact (@lem395314 A B h something_arbitrary (term743 A B h P s x) e' s P x h1 h2). Qed.
Lemma lem395379 {A B : Type'} (something_arbitrary : B) (h : A -> B) (e' : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term789 A B something_arbitrary h P s x e'.
Proof. exact (@lem395378 A B something_arbitrary h e' s P x h1 h2 (@lem395377 A B h P s x)). Qed.
Lemma lem395383 {B : Type'} (something_arbitrary : B) : something_arbitrary = something_arbitrary.
Proof. exact (eq_refl something_arbitrary). Qed.
Lemma lem395384 {A B : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : term790 A B P s x something_arbitrary.
Proof. exact (fun h0 : term791 A P s x => @lem395383 B something_arbitrary). Qed.
Lemma lem395385 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term792 A B h P s x something_arbitrary.
Proof. exact (@lem395379 A B something_arbitrary h something_arbitrary s P x h1 h2). Qed.
Lemma lem395386 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term746 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary).
Proof. exact (@lem395385 A B h something_arbitrary s P x h1 h2 (@lem395384 A B P s x something_arbitrary)). Qed.
Lemma lem395586 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term703 A B h P s x something_arbitrary) = (term703 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term703 A B h P s x something_arbitrary)). Qed.
Lemma lem395587 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : ((term699 A B h P s x something_arbitrary) = (term746 A B h P s x something_arbitrary)) = ((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)).
Proof. exact (MK_COMB (@lem395586 A B h P s x something_arbitrary) (@lem395386 A B h something_arbitrary s P x h1 h2)). Qed.
Lemma lem395988 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : ((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)) = ((term699 A B h P s x something_arbitrary) = (term746 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem395587 A B h something_arbitrary s P x h1 h2)). Qed.
Lemma lem395989 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term794 B _476 _475 _474 _477) = (term795 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem395990 {A B : Type'} (_474 : B) (_475 : Prop) (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) (_477 : B) : (term796 A B h P s x something_arbitrary _475 _474 _477) = (term797 A B _474 _475 h P s x something_arbitrary _477).
Proof. exact (@lem395989 B _474 _475 (term798 A B h P s x something_arbitrary) _477). Qed.
Lemma lem395991 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term799 A B h P s x something_arbitrary) = (term800 A B h P s x something_arbitrary).
Proof. exact (@lem395990 A B (term801 A B h P s x) (term782 A P s x) h P s x something_arbitrary something_arbitrary). Qed.
Lemma lem395992 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term802 A B h P s x something_arbitrary) = (something_arbitrary = (term793 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term802 A B h P s x something_arbitrary)). Qed.
Lemma lem395993 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term803 A P s x) = (term803 A P s x).
Proof. exact (eq_refl (term803 A P s x)). Qed.
Lemma lem395994 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term804 A B h P s x something_arbitrary) = (term805 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem395993 A P s x) (@lem395992 A B h P s x something_arbitrary)). Qed.
Lemma lem395995 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term806 A B something_arbitrary h P s x) = ((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term806 A B something_arbitrary h P s x)). Qed.
Lemma lem395996 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (eq_refl (term807 A P s x)). Qed.
Lemma lem395997 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term808 A B something_arbitrary h P s x) = (term809 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem395996 A P s x) (@lem395995 A B h P s x something_arbitrary)). Qed.
Lemma lem395998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem395999 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term810 A B something_arbitrary h P s x) = (term811 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem395998) (@lem395997 A B h P s x something_arbitrary)). Qed.
Lemma lem396000 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term800 A B h P s x something_arbitrary) = (term812 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem395999 A B h P s x something_arbitrary) (@lem395994 A B h P s x something_arbitrary)). Qed.
Lemma lem396001 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term799 A B h P s x something_arbitrary) = ((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term799 A B h P s x something_arbitrary)). Qed.
Lemma lem396002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem396003 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term813 A B h P s x something_arbitrary) = (term814 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem396002) (@lem396001 A B h P s x something_arbitrary)). Qed.
Lemma lem396004 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term799 A B h P s x something_arbitrary) = (term800 A B h P s x something_arbitrary)) = (((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)) = (term812 A B h P s x something_arbitrary)).
Proof. exact (MK_COMB (@lem396003 A B h P s x something_arbitrary) (@lem396000 A B h P s x something_arbitrary)). Qed.
Lemma lem396005 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)) = (term812 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396004 A B h P s x something_arbitrary) (@lem395991 A B h P s x something_arbitrary)). Qed.
Lemma lem396006 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term812 A B h P s x something_arbitrary) = ((term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem396005 A B h P s x something_arbitrary)). Qed.
Lemma lem396007 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (h1). Qed.
Lemma lem396008 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = ((term782 A P s x) = True).
Proof. exact (@lem7 (term782 A P s x)). Qed.
Lemma lem396009 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : (term782 A P s x) = True.
Proof. exact (EQ_MP (@lem396008 A P s x) (@lem396007 A P s x h1)). Qed.
Lemma lem396010 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term815 A B h P s x something_arbitrary) = (term815 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term815 A B h P s x something_arbitrary)). Qed.
Lemma lem396011 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : (term816 A B h something_arbitrary P s x) = (term817 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem396010 A B h P s x something_arbitrary) (@lem396009 A P s x h1)). Qed.
Lemma lem396012 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term817 A B h P s x something_arbitrary) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term817 A B h P s x something_arbitrary)). Qed.
Lemma lem396013 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) : (term819 A B h something_arbitrary P s x) = (term819 A B h something_arbitrary P s x).
Proof. exact (eq_refl (term819 A B h something_arbitrary P s x)). Qed.
Lemma lem396014 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term816 A B h something_arbitrary P s x) = (term817 A B h P s x something_arbitrary)) = ((term816 A B h something_arbitrary P s x) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary))).
Proof. exact (MK_COMB (@lem396013 A B h something_arbitrary P s x) (@lem396012 A B h P s x something_arbitrary)). Qed.
Lemma lem396015 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term816 A B h something_arbitrary P s x) = ((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term816 A B h something_arbitrary P s x)). Qed.
Lemma lem396016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem396017 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term819 A B h something_arbitrary P s x) = (term820 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem396016) (@lem396015 A B h P s x something_arbitrary)). Qed.
Lemma lem396018 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)).
Proof. exact (eq_refl ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary))). Qed.
Lemma lem396019 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term816 A B h something_arbitrary P s x) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary))) = (((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary))).
Proof. exact (MK_COMB (@lem396017 A B h P s x something_arbitrary) (@lem396018 A B h P s x something_arbitrary)). Qed.
Lemma lem396020 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term816 A B h something_arbitrary P s x) = (term817 A B h P s x something_arbitrary)) = (((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary))).
Proof. exact (TRANS (@lem396014 A B h P s x something_arbitrary) (@lem396019 A B h P s x something_arbitrary)). Qed.
Lemma lem396021 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : ((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)).
Proof. exact (EQ_MP (@lem396020 A B h P s x something_arbitrary) (@lem396011 A B h something_arbitrary P s x h1)). Qed.
Lemma lem396022 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem396021 A B h something_arbitrary P s x h1)). Qed.
Lemma lem396023 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term791 A P s x.
Proof. exact (h1). Qed.
Lemma lem396024 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term821 A P s x.
Proof. exact (@lem82 (term782 A P s x)). Qed.
Lemma lem396025 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : (term782 A P s x) = False.
Proof. exact (@lem396024 A P s x (@lem396023 A P s x h1)). Qed.
Lemma lem396026 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term822 A B h P s x something_arbitrary) = (term822 A B h P s x something_arbitrary).
Proof. exact (eq_refl (term822 A B h P s x something_arbitrary)). Qed.
Lemma lem396027 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : (term823 A B h something_arbitrary P s x) = (term824 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem396026 A B h P s x something_arbitrary) (@lem396025 A P s x h1)). Qed.
Lemma lem396028 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term824 A B h P s x something_arbitrary) = (something_arbitrary = (term825 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term824 A B h P s x something_arbitrary)). Qed.
Lemma lem396029 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) : (term826 A B h something_arbitrary P s x) = (term826 A B h something_arbitrary P s x).
Proof. exact (eq_refl (term826 A B h something_arbitrary P s x)). Qed.
Lemma lem396030 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term823 A B h something_arbitrary P s x) = (term824 A B h P s x something_arbitrary)) = ((term823 A B h something_arbitrary P s x) = (something_arbitrary = (term825 A B h P s x something_arbitrary))).
Proof. exact (MK_COMB (@lem396029 A B h something_arbitrary P s x) (@lem396028 A B h P s x something_arbitrary)). Qed.
Lemma lem396031 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term823 A B h something_arbitrary P s x) = (something_arbitrary = (term793 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (term823 A B h something_arbitrary P s x)). Qed.
Lemma lem396032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem396033 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term826 A B h something_arbitrary P s x) = (term827 A B h P s x something_arbitrary).
Proof. exact (MK_COMB (@lem396032) (@lem396031 A B h P s x something_arbitrary)). Qed.
Lemma lem396034 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (something_arbitrary = (term825 A B h P s x something_arbitrary)) = (something_arbitrary = (term825 A B h P s x something_arbitrary)).
Proof. exact (eq_refl (something_arbitrary = (term825 A B h P s x something_arbitrary))). Qed.
Lemma lem396035 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term823 A B h something_arbitrary P s x) = (something_arbitrary = (term825 A B h P s x something_arbitrary))) = ((something_arbitrary = (term793 A B h P s x something_arbitrary)) = (something_arbitrary = (term825 A B h P s x something_arbitrary))).
Proof. exact (MK_COMB (@lem396033 A B h P s x something_arbitrary) (@lem396034 A B h P s x something_arbitrary)). Qed.
Lemma lem396036 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term823 A B h something_arbitrary P s x) = (term824 A B h P s x something_arbitrary)) = ((something_arbitrary = (term793 A B h P s x something_arbitrary)) = (something_arbitrary = (term825 A B h P s x something_arbitrary))).
Proof. exact (TRANS (@lem396030 A B h P s x something_arbitrary) (@lem396035 A B h P s x something_arbitrary)). Qed.
Lemma lem396037 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : (something_arbitrary = (term793 A B h P s x something_arbitrary)) = (something_arbitrary = (term825 A B h P s x something_arbitrary)).
Proof. exact (EQ_MP (@lem396036 A B h P s x something_arbitrary) (@lem396027 A B h something_arbitrary P s x h1)). Qed.
Lemma lem396038 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : (something_arbitrary = (term825 A B h P s x something_arbitrary)) = (something_arbitrary = (term793 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem396037 A B h something_arbitrary P s x h1)). Qed.
Lemma lem396071 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem396072 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem396071 B t2 t1). Qed.
Lemma lem396073 {A B : Type'} (something_arbitrary : B) (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : (term818 A B h P s x something_arbitrary) = (term743 A B h P s x).
Proof. exact (@lem396072 B something_arbitrary (term743 A B h P s x)). Qed.
Lemma lem396090 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : (term828 A B h P s x) = (term828 A B h P s x).
Proof. exact (eq_refl (term828 A B h P s x)). Qed.
Lemma lem396091 {A B : Type'} (something_arbitrary : B) (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)) = ((term801 A B h P s x) = (term743 A B h P s x)).
Proof. exact (MK_COMB (@lem396090 A B h P s x) (@lem396073 A B something_arbitrary h P s x)). Qed.
Lemma lem396094 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : ((term801 A B h P s x) = (term743 A B h P s x)) = ((term801 A B h P s x) = (term818 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem396091 A B something_arbitrary h P s x)). Qed.
Lemma lem396111 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem396112 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem396111 B t1 t2). Qed.
Lemma lem396113 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (term825 A B h P s x something_arbitrary) = something_arbitrary.
Proof. exact (@lem396112 B (term743 A B h P s x) something_arbitrary). Qed.
Lemma lem396114 {B : Type'} (something_arbitrary : B) : (@eq B something_arbitrary) = (@eq B something_arbitrary).
Proof. exact (eq_refl (@eq B something_arbitrary)). Qed.
Lemma lem396115 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (something_arbitrary = (term825 A B h P s x something_arbitrary)) = (something_arbitrary = something_arbitrary).
Proof. exact (MK_COMB (@lem396114 B something_arbitrary) (@lem396113 A B h P s x something_arbitrary)). Qed.
Lemma lem396117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem396118 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem396117 B x). Qed.
Lemma lem396119 {B : Type'} (something_arbitrary : B) : (something_arbitrary = something_arbitrary) = True.
Proof. exact (@lem396118 B something_arbitrary). Qed.
Lemma lem396120 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : (something_arbitrary = (term825 A B h P s x something_arbitrary)) = True.
Proof. exact (TRANS (@lem396115 A B h P s x something_arbitrary) (@lem396119 B something_arbitrary)). Qed.
Lemma lem396121 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : True = (something_arbitrary = (term825 A B h P s x something_arbitrary)).
Proof. exact (SYM (@lem396120 A B h P s x something_arbitrary)). Qed.
Lemma lem396122 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : something_arbitrary = (term825 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396121 A B h P s x something_arbitrary) (@lem0)). Qed.
Lemma lem396123 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : (term801 A B h P s x) = (term743 A B h P s x)) : (term801 A B h P s x) = (term743 A B h P s x).
Proof. exact (h1). Qed.
Lemma lem396124 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : (term801 A B h P s x) = (term743 A B h P s x)) : (term743 A B h P s x) = (term801 A B h P s x).
Proof. exact (SYM (@lem396123 A B h P s x h1)). Qed.
Lemma lem396125 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : (term743 A B h P s x) = (term801 A B h P s x)) : (term743 A B h P s x) = (term801 A B h P s x).
Proof. exact (h1). Qed.
Lemma lem396126 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : (term743 A B h P s x) = (term801 A B h P s x)) : (term801 A B h P s x) = (term743 A B h P s x).
Proof. exact (SYM (@lem396125 A B h P s x h1)). Qed.
Lemma lem396127 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : ((term801 A B h P s x) = (term743 A B h P s x)) = ((term743 A B h P s x) = (term801 A B h P s x)).
Proof. exact (prop_ext (fun h1 : (term801 A B h P s x) = (term743 A B h P s x) => @lem396124 A B h P s x h1) (fun h1 : (term743 A B h P s x) = (term801 A B h P s x) => @lem396126 A B h P s x h1)). Qed.
Lemma lem396128 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : ((term743 A B h P s x) = (term801 A B h P s x)) = ((term801 A B h P s x) = (term743 A B h P s x)).
Proof. exact (SYM (@lem396127 A B h P s x)). Qed.
Lemma lem396129 (P : nat -> Prop) (h1 : term67 P) : term67 P.
Proof. exact (h1). Qed.
Lemma lem396130 (P : nat -> Prop) (h1 : term67 P) : (term32 P) = (term29 P).
Proof. exact (@lem389869 P (@lem396129 P h1)). Qed.
Lemma lem396136 (P : nat -> Prop) (h1 : term188 P) : term188 P.
Proof. exact (h1). Qed.
Lemma lem396137 (n : nat) (P : nat -> Prop) (h1 : term188 P) : (term240 n P) = (term241 n P).
Proof. exact (@lem394269 n P (@lem396136 P h1)). Qed.
Lemma lem396143 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term596 A s x.
Proof. exact (@lem394512 A s h1 x). Qed.
Lemma lem396144 {A : Type'} (s : type1423 A) (x : A) : (term596 A s x) = ((term597 A s x) = x).
Proof. exact (eq_refl (term596 A s x)). Qed.
Lemma lem396152 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem396190 (n : nat) (P : nat -> Prop) : term538 n P.
Proof. exact (fun h0 : term188 P => @lem396137 n P h0). Qed.
Lemma lem396191 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : term829 A n P s x.
Proof. exact (@lem396190 n (term830 A P s x)). Qed.
Lemma lem396192 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term831 A P s x) = (term784 A P s x).
Proof. exact (eq_refl (term831 A P s x)). Qed.
Lemma lem396193 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem396194 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term832 A P s x) = (term833 A P s x).
Proof. exact (MK_COMB (@lem396193) (@lem396192 A P s x)). Qed.
Lemma lem396195 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term834 A P s x m) = (term711 A P s x m).
Proof. exact (eq_refl (term834 A P s x m)). Qed.
Lemma lem396196 (m : nat) (n : nat) : (term438 m n) = (term438 m n).
Proof. exact (eq_refl (term438 m n)). Qed.
Lemma lem396197 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term835 A n P s x m) = (term725 A n P s x m).
Proof. exact (MK_COMB (@lem396196 m n) (@lem396195 A P s x m)). Qed.
Lemma lem396198 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term836 A n P s x) = (term727 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem396197 A n P s x m)). Qed.
Lemma lem396199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem396200 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term837 A n P s x) = (term729 A n P s x).
Proof. exact (MK_COMB (@lem396199) (@lem396198 A n P s x)). Qed.
Lemma lem396201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem396202 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term838 A n P s x) = (term839 A n P s x).
Proof. exact (MK_COMB (@lem396201) (@lem396200 A n P s x)). Qed.
Lemma lem396203 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term840 A P s x m) = (term841 A P s x m).
Proof. exact (eq_refl (term840 A P s x m)). Qed.
Lemma lem396204 (m : nat) (n : nat) : (term485 m n) = (term485 m n).
Proof. exact (eq_refl (term485 m n)). Qed.
Lemma lem396205 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term842 A n P s x m) = (term843 A n P s x m).
Proof. exact (MK_COMB (@lem396204 m n) (@lem396203 A P s x m)). Qed.
Lemma lem396206 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term844 A n P s x) = (term845 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem396205 A n P s x m)). Qed.
Lemma lem396207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem396208 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term846 A n P s x) = (term847 A n P s x).
Proof. exact (MK_COMB (@lem396207) (@lem396206 A n P s x)). Qed.
Lemma lem396209 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : ((term837 A n P s x) = (term846 A n P s x)) = ((term729 A n P s x) = (term847 A n P s x)).
Proof. exact (MK_COMB (@lem396202 A n P s x) (@lem396208 A n P s x)). Qed.
Lemma lem396210 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term829 A n P s x) = (term848 A n P s x).
Proof. exact (MK_COMB (@lem396194 A P s x) (@lem396209 A n P s x)). Qed.
Lemma lem396211 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : term848 A n P s x.
Proof. exact (EQ_MP (@lem396210 A n P s x) (@lem396191 A n P s x)). Qed.
Lemma lem396213 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem396144 A s x) (@lem396143 A x s h1)). Qed.
Lemma lem396214 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem396213 A x s h1). Qed.
Lemma lem396215 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem396216 {A : Type'} (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : (term784 A P s x) = (P x).
Proof. exact (MK_COMB (@lem396215 A P) (@lem396214 A x s h1)). Qed.
Lemma lem396218 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem396152 A P x) (@lem394332 A P x h1)). Qed.
Lemma lem396219 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term784 A P s x) = True.
Proof. exact (TRANS (@lem396216 A P x s h1) (@lem396218 A P x h2)). Qed.
Lemma lem396220 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : True = (term784 A P s x).
Proof. exact (SYM (@lem396219 A s P x h1 h2)). Qed.
Lemma lem396221 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term784 A P s x.
Proof. exact (EQ_MP (@lem396220 A s P x h1 h2) (@lem0)). Qed.
Lemma lem396222 {A : Type'} (n : nat) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term729 A n P s x) = (term847 A n P s x).
Proof. exact (@lem396211 A n P s x (@lem396221 A s P x h1 h2)). Qed.
Lemma lem396273 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term723 A P s x n) = (term723 A P s x n).
Proof. exact (eq_refl (term723 A P s x n)). Qed.
Lemma lem396274 {A : Type'} (n : nat) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term731 A n P s x) = (term849 A n P s x).
Proof. exact (MK_COMB (@lem396273 A P s x n) (@lem396222 A n s P x h1 h2)). Qed.
Lemma lem396327 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term721 A y s x n) = (term721 A y s x n).
Proof. exact (eq_refl (term721 A y s x n)). Qed.
Lemma lem396328 {A : Type'} (y : A) (n : nat) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term733 A y n P s x) = (term850 A y n P s x).
Proof. exact (MK_COMB (@lem396327 A y s x n) (@lem396274 A n s P x h1 h2)). Qed.
Lemma lem396385 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term735 A y P s x) = (term851 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem396328 A y n s P x h1 h2)). Qed.
Lemma lem396442 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem396443 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term737 A y P s x) = (term852 A y P s x).
Proof. exact (MK_COMB (@lem396442) (@lem396385 A y s P x h1 h2)). Qed.
Lemma lem396449 (P : nat -> Prop) : term1 P.
Proof. exact (fun h0 : term67 P => @lem396130 P h0). Qed.
Lemma lem396450 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term853 A y P s x.
Proof. exact (@lem396449 (term854 A y P s x)). Qed.
Lemma lem396451 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term855 A y P s x) = (term856 A y P s x).
Proof. exact (eq_refl (term855 A y P s x)). Qed.
Lemma lem396452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem396453 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term857 A y P s x) = (term858 A y P s x).
Proof. exact (MK_COMB (@lem396452) (@lem396451 A y P s x)). Qed.
Lemma lem396454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem396455 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term859 A y P s x) = (term860 A y P s x).
Proof. exact (MK_COMB (@lem396454) (@lem396453 A y P s x)). Qed.
Lemma lem396456 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term861 A y P s x n) = (term850 A y n P s x).
Proof. exact (eq_refl (term861 A y P s x n)). Qed.
Lemma lem396457 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term862 A y P s x) = (term851 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem396456 A y n P s x)). Qed.
Lemma lem396458 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem396459 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term863 A y P s x) = (term852 A y P s x).
Proof. exact (MK_COMB (@lem396458) (@lem396457 A y P s x)). Qed.
Lemma lem396460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem396461 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term864 A y P s x) = (term865 A y P s x).
Proof. exact (MK_COMB (@lem396460) (@lem396459 A y P s x)). Qed.
Lemma lem396462 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term866 A y P s x n) = (term867 A y n P s x).
Proof. exact (eq_refl (term866 A y P s x n)). Qed.
Lemma lem396463 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term868 A y P s x) = (term854 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem396462 A y n P s x)). Qed.
Lemma lem396464 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem396465 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term869 A y P s x) = (term870 A y P s x).
Proof. exact (MK_COMB (@lem396464) (@lem396463 A y P s x)). Qed.
Lemma lem396466 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : ((term863 A y P s x) = (term869 A y P s x)) = ((term852 A y P s x) = (term870 A y P s x)).
Proof. exact (MK_COMB (@lem396461 A y P s x) (@lem396465 A y P s x)). Qed.
Lemma lem396467 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term853 A y P s x) = (term871 A y P s x).
Proof. exact (MK_COMB (@lem396455 A y P s x) (@lem396466 A y P s x)). Qed.
Lemma lem396468 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term871 A y P s x.
Proof. exact (EQ_MP (@lem396467 A y P s x) (@lem396450 A y P s x)). Qed.
Lemma lem396474 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem396144 A s x) (@lem396143 A x s h1)). Qed.
Lemma lem396475 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem396474 A x s h1). Qed.
Lemma lem396476 {A : Type'} (y : A) : (@eq A y) = (@eq A y).
Proof. exact (eq_refl (@eq A y)). Qed.
Lemma lem396477 {A : Type'} (y : A) (x : A) (s : type1423 A) (h1 : term608 A s) : (y = (term597 A s x)) = (y = x).
Proof. exact (MK_COMB (@lem396476 A y) (@lem396475 A x s h1)). Qed.
Lemma lem396480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem396481 {A : Type'} (y : A) (x : A) (s : type1423 A) (h1 : term608 A s) : (term872 A y s x) = (term873 A y x).
Proof. exact (MK_COMB (@lem396480) (@lem396477 A y x s h1)). Qed.
Lemma lem396487 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem396144 A s x) (@lem396143 A x s h1)). Qed.
Lemma lem396488 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem396487 A x s h1). Qed.
Lemma lem396489 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem396490 {A : Type'} (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : (term784 A P s x) = (P x).
Proof. exact (MK_COMB (@lem396489 A P) (@lem396488 A x s h1)). Qed.
Lemma lem396492 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem396152 A P x) (@lem394332 A P x h1)). Qed.
Lemma lem396493 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term784 A P s x) = True.
Proof. exact (TRANS (@lem396490 A P x s h1) (@lem396492 A P x h2)). Qed.
Lemma lem396494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem396495 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term768 A P s x) = (~ True).
Proof. exact (MK_COMB (@lem396494) (@lem396493 A s P x h1 h2)). Qed.
Lemma lem396497 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem396498 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term768 A P s x) = False.
Proof. exact (TRANS (@lem396495 A s P x h1 h2) (@lem396497)). Qed.
Lemma lem396499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem396500 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term874 A P s x) = (and False).
Proof. exact (MK_COMB (@lem396499) (@lem396498 A s P x h1 h2)). Qed.
Lemma lem396551 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term875 A P s x) = (term875 A P s x).
Proof. exact (eq_refl (term875 A P s x)). Qed.
Lemma lem396552 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term876 A P s x) = (term877 A P s x).
Proof. exact (MK_COMB (@lem396500 A s P x h1 h2) (@lem396551 A P s x)). Qed.
Lemma lem396554 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem396555 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term877 A P s x) = False.
Proof. exact (@lem396554 (term875 A P s x)). Qed.
Lemma lem396556 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term876 A P s x) = False.
Proof. exact (TRANS (@lem396552 A s P x h1 h2) (@lem396555 A P s x)). Qed.
Lemma lem396557 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term856 A y P s x) = (term878 A y x).
Proof. exact (MK_COMB (@lem396481 A y x s h1) (@lem396556 A s P x h1 h2)). Qed.
Lemma lem396559 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem396560 {A : Type'} (y : A) (x : A) : (term878 A y x) = False.
Proof. exact (@lem396559 (y = x)). Qed.
Lemma lem396561 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term856 A y P s x) = False.
Proof. exact (TRANS (@lem396557 A y s P x h1 h2) (@lem396560 A y x)). Qed.
Lemma lem396562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem396563 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term858 A y P s x) = (~ False).
Proof. exact (MK_COMB (@lem396562) (@lem396561 A y s P x h1 h2)). Qed.
Lemma lem396565 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem396566 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term858 A y P s x) = True.
Proof. exact (TRANS (@lem396563 A y s P x h1 h2) (@lem396565)). Qed.
Lemma lem396567 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : True = (term858 A y P s x).
Proof. exact (SYM (@lem396566 A y s P x h1 h2)). Qed.
Lemma lem396568 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term858 A y P s x.
Proof. exact (EQ_MP (@lem396567 A y s P x h1 h2) (@lem0)). Qed.
Lemma lem396569 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term852 A y P s x) = (term870 A y P s x).
Proof. exact (@lem396468 A y P s x (@lem396568 A y s P x h1 h2)). Qed.
Lemma lem396651 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term737 A y P s x) = (term870 A y P s x).
Proof. exact (TRANS (@lem396443 A y s P x h1 h2) (@lem396569 A y s P x h1 h2)). Qed.
Lemma lem396652 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term739 A P s x) = (term879 A P s x).
Proof. exact (fun_ext (fun y : A => @lem396651 A y s P x h1 h2)). Qed.
Lemma lem396734 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem396735 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term741 A P s x) = (term880 A P s x).
Proof. exact (MK_COMB (@lem396734 A) (@lem396652 A s P x h1 h2)). Qed.
Lemma lem396817 {A B : Type'} (h : A -> B) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem396818 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term743 A B h P s x) = (term801 A B h P s x).
Proof. exact (MK_COMB (@lem396817 A B h) (@lem396735 A s P x h1 h2)). Qed.
Lemma lem396900 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem396901 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term881 A B h P s x) = (term828 A B h P s x).
Proof. exact (MK_COMB (@lem396900 B) (@lem396818 A B h s P x h1 h2)). Qed.
Lemma lem397064 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : (term801 A B h P s x) = (term801 A B h P s x).
Proof. exact (eq_refl (term801 A B h P s x)). Qed.
Lemma lem397065 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : ((term743 A B h P s x) = (term801 A B h P s x)) = ((term801 A B h P s x) = (term801 A B h P s x)).
Proof. exact (MK_COMB (@lem396901 A B h s P x h1 h2) (@lem397064 A B h P s x)). Qed.
Lemma lem397067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem397068 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem397067 B x). Qed.
Lemma lem397069 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) : ((term801 A B h P s x) = (term801 A B h P s x)) = True.
Proof. exact (@lem397068 B (term801 A B h P s x)). Qed.
Lemma lem397070 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : ((term743 A B h P s x) = (term801 A B h P s x)) = True.
Proof. exact (TRANS (@lem397065 A B h s P x h1 h2) (@lem397069 A B h P s x)). Qed.
Lemma lem397071 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : True = ((term743 A B h P s x) = (term801 A B h P s x)).
Proof. exact (SYM (@lem397070 A B h s P x h1 h2)). Qed.
Lemma lem397072 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term743 A B h P s x) = (term801 A B h P s x).
Proof. exact (EQ_MP (@lem397071 A B h s P x h1 h2) (@lem0)). Qed.
Lemma lem397073 {A B : Type'} (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term801 A B h P s x) = (term743 A B h P s x).
Proof. exact (EQ_MP (@lem396128 A B h P s x) (@lem397072 A B h s P x h1 h2)). Qed.
Lemma lem397074 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term801 A B h P s x) = (term818 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396094 A B h P s x something_arbitrary) (@lem397073 A B h s P x h1 h2)). Qed.
Lemma lem397075 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : something_arbitrary = (term793 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396038 A B h something_arbitrary P s x h1) (@lem396122 A B h P s x something_arbitrary)). Qed.
Lemma lem397076 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : (term791 A P s x) = (something_arbitrary = (term793 A B h P s x something_arbitrary)).
Proof. exact (prop_ext (fun h2 : term791 A P s x => @lem397075 A B h something_arbitrary P s x h1) (fun h2 : something_arbitrary = (term793 A B h P s x something_arbitrary) => @lem396023 A P s x h1)). Qed.
Lemma lem397077 {A B : Type'} (h : A -> B) (something_arbitrary : B) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : something_arbitrary = (term793 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem397076 A B h something_arbitrary P s x h1) (@lem396023 A P s x h1)). Qed.
Lemma lem397078 {A B : Type'} (h : A -> B) (P : A -> Prop) (s : type1423 A) (x : A) (something_arbitrary : B) : term805 A B h P s x something_arbitrary.
Proof. exact (fun h0 : term791 A P s x => @lem397077 A B h something_arbitrary P s x h0). Qed.
Lemma lem397079 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : P x) : (term801 A B h P s x) = (term793 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396022 A B h something_arbitrary P s x h2) (@lem397074 A B h something_arbitrary s P x h1 h3)). Qed.
Lemma lem397080 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : P x) : (term782 A P s x) = ((term801 A B h P s x) = (term793 A B h P s x something_arbitrary)).
Proof. exact (prop_ext (fun h4 : term782 A P s x => @lem397079 A B h something_arbitrary s P x h1 h2 h3) (fun h4 : (term801 A B h P s x) = (term793 A B h P s x something_arbitrary) => @lem396007 A P s x h2)). Qed.
Lemma lem397081 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : P x) : (term801 A B h P s x) = (term793 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem397080 A B h something_arbitrary s P x h1 h2 h3) (@lem396007 A P s x h2)). Qed.
Lemma lem397082 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term809 A B h P s x something_arbitrary.
Proof. exact (fun h0 : term782 A P s x => @lem397081 A B h something_arbitrary s P x h1 h0 h2). Qed.
Lemma lem397083 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : term812 A B h P s x something_arbitrary.
Proof. exact (conj (@lem397082 A B h something_arbitrary s P x h1 h2) (@lem397078 A B h P s x something_arbitrary)). Qed.
Lemma lem397084 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term699 A B h P s x something_arbitrary) = (term793 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem396006 A B h P s x something_arbitrary) (@lem397083 A B h something_arbitrary s P x h1 h2)). Qed.
Lemma lem397085 {A B : Type'} (h : A -> B) (something_arbitrary : B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : P x) : (term699 A B h P s x something_arbitrary) = (term746 A B h P s x something_arbitrary).
Proof. exact (EQ_MP (@lem395988 A B h something_arbitrary s P x h1 h2) (@lem397084 A B h something_arbitrary s P x h1 h2)). Qed.
Lemma lem397086 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term794 B _476 _475 _474 _477) = (term795 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem397087 {A B : Type'} (_474 : B) (_475 : Prop) (h : A -> B) (x : A) (_477 : B) : (term882 A B h x _475 _474 _477) = (term883 A B _474 _475 h x _477).
Proof. exact (@lem397086 B _474 _475 (term884 A B h x) _477). Qed.
Lemma lem397088 {A B : Type'} (P : A -> Prop) (s : type1423 A) (h : A -> B) (x : A) (something_arbitrary : B) : (term885 A B h P s x something_arbitrary) = (term886 A B P s h x something_arbitrary).
Proof. exact (@lem397087 A B (term801 A B h P s x) (term782 A P s x) h x something_arbitrary). Qed.
Lemma lem397089 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term887 A B h x something_arbitrary) = (something_arbitrary = (h x)).
Proof. exact (eq_refl (term887 A B h x something_arbitrary)). Qed.
Lemma lem397090 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term803 A P s x) = (term803 A P s x).
Proof. exact (eq_refl (term803 A P s x)). Qed.
Lemma lem397091 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term888 A B P s h x something_arbitrary) = (term889 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397090 A P s x) (@lem397089 A B something_arbitrary h x)). Qed.
Lemma lem397092 {A B : Type'} (P : A -> Prop) (s : type1423 A) (h : A -> B) (x : A) : (term890 A B h P s x) = ((term801 A B h P s x) = (h x)).
Proof. exact (eq_refl (term890 A B h P s x)). Qed.
Lemma lem397093 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (eq_refl (term807 A P s x)). Qed.
Lemma lem397094 {A B : Type'} (P : A -> Prop) (s : type1423 A) (h : A -> B) (x : A) : (term891 A B h P s x) = (term892 A B P s h x).
Proof. exact (MK_COMB (@lem397093 A P s x) (@lem397092 A B P s h x)). Qed.
Lemma lem397095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem397096 {A B : Type'} (P : A -> Prop) (s : type1423 A) (h : A -> B) (x : A) : (term893 A B h P s x) = (term894 A B P s h x).
Proof. exact (MK_COMB (@lem397095) (@lem397094 A B P s h x)). Qed.
Lemma lem397097 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term886 A B P s h x something_arbitrary) = (term895 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397096 A B P s h x) (@lem397091 A B P s something_arbitrary h x)). Qed.
Lemma lem397098 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term885 A B h P s x something_arbitrary) = ((term699 A B h P s x something_arbitrary) = (h x)).
Proof. exact (eq_refl (term885 A B h P s x something_arbitrary)). Qed.
Lemma lem397099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem397100 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term896 A B h P s x something_arbitrary) = (term897 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397099) (@lem397098 A B P s something_arbitrary h x)). Qed.
Lemma lem397101 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : ((term885 A B h P s x something_arbitrary) = (term886 A B P s h x something_arbitrary)) = (((term699 A B h P s x something_arbitrary) = (h x)) = (term895 A B P s something_arbitrary h x)).
Proof. exact (MK_COMB (@lem397100 A B P s something_arbitrary h x) (@lem397097 A B P s something_arbitrary h x)). Qed.
Lemma lem397102 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : ((term699 A B h P s x something_arbitrary) = (h x)) = (term895 A B P s something_arbitrary h x).
Proof. exact (EQ_MP (@lem397101 A B P s something_arbitrary h x) (@lem397088 A B P s h x something_arbitrary)). Qed.
Lemma lem397103 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term895 A B P s something_arbitrary h x) = ((term699 A B h P s x something_arbitrary) = (h x)).
Proof. exact (SYM (@lem397102 A B P s something_arbitrary h x)). Qed.
Lemma lem397104 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (h1). Qed.
Lemma lem397121 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term791 A P s x.
Proof. exact (h1). Qed.
Lemma lem397139 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem397140 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (something_arbitrary = (h x)) = (term898 A B something_arbitrary h x).
Proof. exact (@lem397139 (something_arbitrary = (h x))). Qed.
Lemma lem397141 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term898 A B something_arbitrary h x) = (something_arbitrary = (h x)).
Proof. exact (SYM (@lem397140 A B something_arbitrary h x)). Qed.
Lemma lem397142 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term899 A B something_arbitrary h x) : term899 A B something_arbitrary h x.
Proof. exact (h1). Qed.
Lemma lem397145 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term900 A B g P s something_arbitrary h x) : term900 A B g P s something_arbitrary h x.
Proof. exact (h1). Qed.
Lemma lem397146 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term901 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term900 A B g P s something_arbitrary h x => @lem397145 A B g P s something_arbitrary h x h0). Qed.
Lemma lem397147 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term901 A B g P s something_arbitrary h x) : term901 A B g P s something_arbitrary h x.
Proof. exact (h1). Qed.
Lemma lem397148 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term900 A B g P s something_arbitrary h x) : term900 A B g P s something_arbitrary h x.
Proof. exact (h1). Qed.
Lemma lem397149 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term900 A B g P s something_arbitrary h x) (h2 : term901 A B g P s something_arbitrary h x) : term900 A B g P s something_arbitrary h x.
Proof. exact (@lem397147 A B g P s something_arbitrary h x h2 (@lem397148 A B g P s something_arbitrary h x h1)). Qed.
Lemma lem397150 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term900 A B g P s something_arbitrary h x) : term902 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term901 A B g P s something_arbitrary h x => @lem397149 A B g P s something_arbitrary h x h1 h0). Qed.
Lemma lem397151 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term901 A B g P s something_arbitrary h x) : term901 A B g P s something_arbitrary h x.
Proof. exact (h1). Qed.
Lemma lem397152 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term900 A B g P s something_arbitrary h x) (h2 : term901 A B g P s something_arbitrary h x) : term900 A B g P s something_arbitrary h x.
Proof. exact (@lem397150 A B g P s something_arbitrary h x h1 (@lem397151 A B g P s something_arbitrary h x h2)). Qed.
Lemma lem397153 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term901 A B g P s something_arbitrary h x) : term901 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term900 A B g P s something_arbitrary h x => @lem397152 A B g P s something_arbitrary h x h0 h1). Qed.
Lemma lem397154 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term903 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term901 A B g P s something_arbitrary h x => @lem397153 A B g P s something_arbitrary h x h0). Qed.
Lemma lem397157 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term901 A B g P s something_arbitrary h x.
Proof. exact (@lem397154 A B g P s something_arbitrary h x (@lem397146 A B g P s something_arbitrary h x)). Qed.
Lemma lem397158 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term901 A B g P s something_arbitrary h x.
Proof. exact (@lem397157 A B g P s something_arbitrary h x). Qed.
Lemma lem397208 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem397209 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term898 A B something_arbitrary h x) = (term904 A B something_arbitrary h x).
Proof. exact (@lem397208 (term899 A B something_arbitrary h x)). Qed.
Lemma lem397211 (t : Prop) : (term198 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem397212 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term904 A B something_arbitrary h x) = (something_arbitrary = (h x)).
Proof. exact (@lem397211 (something_arbitrary = (h x))). Qed.
Lemma lem397213 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term898 A B something_arbitrary h x) = (something_arbitrary = (h x)).
Proof. exact (TRANS (@lem397209 A B something_arbitrary h x) (@lem397212 A B something_arbitrary h x)). Qed.
Lemma lem397214 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term803 A P s x) = (term803 A P s x).
Proof. exact (eq_refl (term803 A P s x)). Qed.
Lemma lem397215 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term905 A B P s something_arbitrary h x) = (term889 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397214 A P s x) (@lem397213 A B something_arbitrary h x)). Qed.
Lemma lem397218 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem397219 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term907 A B P s something_arbitrary h x) = (term908 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397218 A P x) (@lem397215 A B P s something_arbitrary h x)). Qed.
Lemma lem397222 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (eq_refl (term909 A g s)). Qed.
Lemma lem397223 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term910 A B g P s something_arbitrary h x) = (term911 A B g P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397222 A g s) (@lem397219 A B P s something_arbitrary h x)). Qed.
Lemma lem397226 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (eq_refl (term912 A s)). Qed.
Lemma lem397227 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term900 A B g P s something_arbitrary h x) = (term913 A B g P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397226 A s) (@lem397223 A B g P s something_arbitrary h x)). Qed.
Lemma lem397230 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term914 A B P s something_arbitrary h x) = (term915 A B P s something_arbitrary h x).
Proof. exact (fun_ext (fun g : A -> A => @lem397227 A B g P s something_arbitrary h x)). Qed.
Lemma lem397231 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem397232 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term916 A B P s something_arbitrary h x) = (term917 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397231 A) (@lem397230 A B P s something_arbitrary h x)). Qed.
Lemma lem397237 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term918 A B s something_arbitrary h x) = (term919 A B s something_arbitrary h x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem397232 A B P s something_arbitrary h x)). Qed.
Lemma lem397238 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem397239 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term920 A B s something_arbitrary h x) = (term921 A B s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397238 A) (@lem397237 A B s something_arbitrary h x)). Qed.
Lemma lem397244 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term922 A B something_arbitrary h x) = (term923 A B something_arbitrary h x).
Proof. exact (fun_ext (fun s : type1423 A => @lem397239 A B s something_arbitrary h x)). Qed.
Lemma lem397245 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem397246 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term924 A B something_arbitrary h x) = (term925 A B something_arbitrary h x).
Proof. exact (MK_COMB (@lem397245 A) (@lem397244 A B something_arbitrary h x)). Qed.
Lemma lem397251 {A B : Type'} (h : A -> B) (x : A) : (term926 A B h x) = (term927 A B h x).
Proof. exact (fun_ext (fun something_arbitrary : B => @lem397246 A B something_arbitrary h x)). Qed.
Lemma lem397252 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem397253 {A B : Type'} (h : A -> B) (x : A) : (term928 A B h x) = (term929 A B h x).
Proof. exact (MK_COMB (@lem397252 B) (@lem397251 A B h x)). Qed.
Lemma lem397258 {A B : Type'} (x : A) : (term930 A B x) = (term931 A B x).
Proof. exact (fun_ext (fun h : A -> B => @lem397253 A B h x)). Qed.
Lemma lem397259 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem397260 {A B : Type'} (x : A) : (term932 A B x) = (term933 A B x).
Proof. exact (MK_COMB (@lem397259 A B) (@lem397258 A B x)). Qed.
Lemma lem397265 {A B : Type'} : (term934 A B) = (term935 A B).
Proof. exact (fun_ext (fun x : A => @lem397260 A B x)). Qed.
Lemma lem397266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397275 {A B : Type'} : (term936 A B) = (term937 A B).
Proof. exact (MK_COMB (@lem397266 A) (@lem397265 A B)). Qed.
Lemma lem397276 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (something_arbitrary = (h x)) = (something_arbitrary = (h x)).
Proof. exact (eq_refl (something_arbitrary = (h x))). Qed.
Lemma lem397279 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term779 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term779 A P s x n)). Qed.
Lemma lem397280 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term766 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem397279 A P s x n)). Qed.
Lemma lem397281 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem397282 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem397281) (@lem397280 A P s x)). Qed.
Lemma lem397283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem397284 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term791 A P s x) = (term791 A P s x).
Proof. exact (MK_COMB (@lem397283) (@lem397282 A P s x)). Qed.
Lemma lem397285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397286 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term803 A P s x) = (term803 A P s x).
Proof. exact (MK_COMB (@lem397285) (@lem397284 A P s x)). Qed.
Lemma lem397287 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term889 A B P s something_arbitrary h x) = (term889 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397286 A P s x) (@lem397276 A B something_arbitrary h x)). Qed.
Lemma lem397292 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem397293 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term908 A B P s something_arbitrary h x) = (term908 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397292 A P x) (@lem397287 A B P s something_arbitrary h x)). Qed.
Lemma lem397294 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : ((term687 A s g x n) = (term635 A s x n)) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl ((term687 A s g x n) = (term635 A s x n))). Qed.
Lemma lem397295 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term938 A g s n) = (term938 A g s n).
Proof. exact (fun_ext (fun x : A => @lem397294 A g s x n)). Qed.
Lemma lem397296 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397297 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term657 A g s n) = (term657 A g s n).
Proof. exact (MK_COMB (@lem397296 A) (@lem397295 A g s n)). Qed.
Lemma lem397298 {A : Type'} (g : A -> A) (s : type1423 A) : (term651 A g s) = (term651 A g s).
Proof. exact (fun_ext (fun n : nat => @lem397297 A g s n)). Qed.
Lemma lem397299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem397300 {A : Type'} (g : A -> A) (s : type1423 A) : (term649 A g s) = (term649 A g s).
Proof. exact (MK_COMB (@lem397299) (@lem397298 A g s)). Qed.
Lemma lem397301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397302 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (MK_COMB (@lem397301) (@lem397300 A g s)). Qed.
Lemma lem397303 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term911 A B g P s something_arbitrary h x) = (term911 A B g P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397302 A g s) (@lem397293 A B P s something_arbitrary h x)). Qed.
Lemma lem397304 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem397305 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem397304 A s x)). Qed.
Lemma lem397306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397307 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem397306 A) (@lem397305 A s)). Qed.
Lemma lem397308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397309 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (MK_COMB (@lem397308) (@lem397307 A s)). Qed.
Lemma lem397310 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term913 A B g P s something_arbitrary h x) = (term913 A B g P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397309 A s) (@lem397303 A B g P s something_arbitrary h x)). Qed.
Lemma lem397311 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term915 A B P s something_arbitrary h x) = (term915 A B P s something_arbitrary h x).
Proof. exact (fun_ext (fun g : A -> A => @lem397310 A B g P s something_arbitrary h x)). Qed.
Lemma lem397312 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem397313 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term917 A B P s something_arbitrary h x) = (term917 A B P s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397312 A) (@lem397311 A B P s something_arbitrary h x)). Qed.
Lemma lem397314 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term919 A B s something_arbitrary h x) = (term919 A B s something_arbitrary h x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem397313 A B P s something_arbitrary h x)). Qed.
Lemma lem397315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem397316 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term921 A B s something_arbitrary h x) = (term921 A B s something_arbitrary h x).
Proof. exact (MK_COMB (@lem397315 A) (@lem397314 A B s something_arbitrary h x)). Qed.
Lemma lem397317 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term923 A B something_arbitrary h x) = (term923 A B something_arbitrary h x).
Proof. exact (fun_ext (fun s : type1423 A => @lem397316 A B s something_arbitrary h x)). Qed.
Lemma lem397318 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem397319 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term925 A B something_arbitrary h x) = (term925 A B something_arbitrary h x).
Proof. exact (MK_COMB (@lem397318 A) (@lem397317 A B something_arbitrary h x)). Qed.
Lemma lem397320 {A B : Type'} (h : A -> B) (x : A) : (term927 A B h x) = (term927 A B h x).
Proof. exact (fun_ext (fun something_arbitrary : B => @lem397319 A B something_arbitrary h x)). Qed.
Lemma lem397321 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem397322 {A B : Type'} (h : A -> B) (x : A) : (term929 A B h x) = (term929 A B h x).
Proof. exact (MK_COMB (@lem397321 B) (@lem397320 A B h x)). Qed.
Lemma lem397323 {A B : Type'} (x : A) : (term931 A B x) = (term931 A B x).
Proof. exact (fun_ext (fun h : A -> B => @lem397322 A B h x)). Qed.
Lemma lem397324 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem397325 {A B : Type'} (x : A) : (term933 A B x) = (term933 A B x).
Proof. exact (MK_COMB (@lem397324 A B) (@lem397323 A B x)). Qed.
Lemma lem397326 {A B : Type'} : (term935 A B) = (term935 A B).
Proof. exact (fun_ext (fun x : A => @lem397325 A B x)). Qed.
Lemma lem397327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397328 {A B : Type'} : (term937 A B) = (term937 A B).
Proof. exact (MK_COMB (@lem397327 A) (@lem397326 A B)). Qed.
Lemma lem397399 {A B : Type'} : (term936 A B) = (term937 A B).
Proof. exact (TRANS (@lem397275 A B) (@lem397328 A B)). Qed.
Lemma lem397400 {A B : Type'} : (term937 A B) = (term936 A B).
Proof. exact (SYM (@lem397399 A B)). Qed.
Lemma lem397401 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (h1). Qed.
Lemma lem397404 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term791 A P s x.
Proof. exact (h1). Qed.
Lemma lem397406 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem397407 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (something_arbitrary = (h x)) = (term898 A B something_arbitrary h x).
Proof. exact (@lem397406 (something_arbitrary = (h x))). Qed.
Lemma lem397408 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term898 A B something_arbitrary h x) = (something_arbitrary = (h x)).
Proof. exact (SYM (@lem397407 A B something_arbitrary h x)). Qed.
Lemma lem397410 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem397411 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem397410 A s x)). Qed.
Lemma lem397412 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397421 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem397412 A) (@lem397411 A s)). Qed.
Lemma lem397422 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem397421 A s) (@lem397401 A s h1)). Qed.
Lemma lem397448 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem397451 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term939 A P s x n) = (term841 A P s x n).
Proof. exact (@lem16933 (term841 A P s x n)). Qed.
Lemma lem397452 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem397453 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term791 A P s x) = (term940 A P s x).
Proof. exact (@lem397452 (term766 A P s x)). Qed.
Lemma lem397454 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term778 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term778 A P s x n)). Qed.
Lemma lem397455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem397456 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term941 A P s x n) = (term939 A P s x n).
Proof. exact (MK_COMB (@lem397455) (@lem397454 A P s x n)). Qed.
Lemma lem397457 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term941 A P s x n) = (term841 A P s x n).
Proof. exact (TRANS (@lem397456 A P s x n) (@lem397451 A P s x n)). Qed.
Lemma lem397458 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term942 A P s x) = (term830 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem397457 A P s x n)). Qed.
Lemma lem397459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem397460 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term940 A P s x) = (term943 A P s x).
Proof. exact (MK_COMB (@lem397459) (@lem397458 A P s x)). Qed.
Lemma lem397469 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term791 A P s x) = (term943 A P s x).
Proof. exact (TRANS (@lem397453 A P s x) (@lem397460 A P s x)). Qed.
Lemma lem397470 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term943 A P s x.
Proof. exact (EQ_MP (@lem397469 A P s x) (@lem397404 A P s x h1)). Qed.
Lemma lem397487 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem397488 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem397487 A s x)). Qed.
Lemma lem397489 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397490 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem397489 A) (@lem397488 A s)). Qed.
Lemma lem397491 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem397490 A s) (@lem397422 A s h1)). Qed.
Lemma lem397521 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem397528 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term841 A P s x n) = (term841 A P s x n).
Proof. exact (eq_refl (term841 A P s x n)). Qed.
Lemma lem397529 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term830 A P s x) = (term830 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem397528 A P s x n)). Qed.
Lemma lem397530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem397531 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term943 A P s x) = (term943 A P s x).
Proof. exact (MK_COMB (@lem397530) (@lem397529 A P s x)). Qed.
Lemma lem397532 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term943 A P s x.
Proof. exact (EQ_MP (@lem397531 A P s x) (@lem397470 A P s x h1)). Qed.
Lemma lem397544 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem397545 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem397544 A s x)). Qed.
Lemma lem397546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397548 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem397546 A) (@lem397545 A s)). Qed.
Lemma lem397549 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem397548 A s) (@lem397491 A s h1)). Qed.
Lemma lem397563 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem397565 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term841 A P s x n) = (term841 A P s x n).
Proof. exact (eq_refl (term841 A P s x n)). Qed.
Lemma lem397566 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term830 A P s x) = (term830 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem397565 A P s x n)). Qed.
Lemma lem397567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem397569 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term943 A P s x) = (term943 A P s x).
Proof. exact (MK_COMB (@lem397567) (@lem397566 A P s x)). Qed.
Lemma lem397570 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term943 A P s x.
Proof. exact (EQ_MP (@lem397569 A P s x) (@lem397532 A P s x h1)). Qed.
Lemma lem397575 {A : Type'} (_8338 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8338.
Proof. exact (@lem397549 A s h1 _8338). Qed.
Lemma lem397576 {A : Type'} (s : type1423 A) (_8338 : A) : (term596 A s _8338) = ((term597 A s _8338) = _8338).
Proof. exact (eq_refl (term596 A s _8338)). Qed.
Lemma lem397584 {A : Type'} (_8341 : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term840 A P s x _8341.
Proof. exact (@lem397570 A P s x h1 _8341). Qed.
Lemma lem397585 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8341 : nat) : (term840 A P s x _8341) = (term841 A P s x _8341).
Proof. exact (eq_refl (term840 A P s x _8341)). Qed.
Lemma lem397592 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem397597 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem397598 {A : Type'} (_8342 : A) (_8343 : A) (h1 : _8342 = _8343) : _8342 = _8343.
Proof. exact (h1). Qed.
Lemma lem397599 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) (h1 : _8342 = _8343) : (P _8342) = (P _8343).
Proof. exact (MK_COMB (@lem397597 A P) (@lem397598 A _8342 _8343 h1)). Qed.
Lemma lem397601 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem397602 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : term944 A _8343 P _8342.
Proof. exact (@lem397601 (P _8343) (P _8342)). Qed.
Lemma lem397603 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) (h1 : _8342 = _8343) : term945 A _8343 P _8342.
Proof. exact (@lem397602 A _8343 P _8342 (@lem397599 A P _8342 _8343 h1)). Qed.
Lemma lem397604 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : term946 A _8343 P _8342.
Proof. exact (fun h0 : _8342 = _8343 => @lem397603 A P _8342 _8343 h0). Qed.
Lemma lem397606 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem397607 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term946 A _8343 P _8342) = (term947 A _8343 P _8342).
Proof. exact (@lem397606 (_8342 = _8343) (term945 A _8343 P _8342)). Qed.
Lemma lem397608 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : term947 A _8343 P _8342.
Proof. exact (EQ_MP (@lem397607 A _8343 P _8342) (@lem397604 A _8343 P _8342)). Qed.
Lemma lem397663 {A : Type'} (_8338 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8338) = _8338.
Proof. exact (EQ_MP (@lem397576 A s _8338) (@lem397575 A _8338 s h1)). Qed.
Lemma lem397664 {A : Type'} (_8338 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8338) = _8338.
Proof. exact (@lem397663 A _8338 s h1). Qed.
Lemma lem397665 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem397664 A x s h1). Qed.
Lemma lem397666 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem397665 A x s h1). Qed.
Lemma lem397668 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem397669 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem397668 ((term597 A s x) = x)). Qed.
Lemma lem397670 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem397669 A s x) (@lem397666 A x s h1)). Qed.
Lemma lem397672 {A : Type'} (_8341 : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term841 A P s x _8341.
Proof. exact (EQ_MP (@lem397585 A P s x _8341) (@lem397584 A _8341 P s x h1)). Qed.
Lemma lem397673 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term784 A P s x.
Proof. exact (@lem397672 A (NUMERAL 0) P s x h1). Qed.
Lemma lem397674 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem397673 A P s x h1). Qed.
Lemma lem397676 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem397677 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem397676 (term784 A P s x)). Qed.
Lemma lem397678 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term791 A P s x) : term784 A P s x.
Proof. exact (EQ_MP (@lem397677 A P s x) (@lem397674 A P s x h1)). Qed.
Lemma lem397684 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem397685 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term947 A _8343 P _8342) = (term951 A _8343 P _8342).
Proof. exact (@lem397684 (P _8343) (term952 A _8342 _8343) (term554 A P _8342)). Qed.
Lemma lem397699 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem397700 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term953 A _8343 P _8342) = (term954 A P _8342 _8343).
Proof. exact (@lem397699 (term554 A P _8342) (term952 A _8342 _8343)). Qed.
Lemma lem397708 {A : Type'} (P : A -> Prop) (_8343 : A) : (term955 A P _8343) = (term955 A P _8343).
Proof. exact (eq_refl (term955 A P _8343)). Qed.
Lemma lem397709 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term951 A _8343 P _8342) = (term956 A P _8342 _8343).
Proof. exact (MK_COMB (@lem397708 A P _8343) (@lem397700 A P _8342 _8343)). Qed.
Lemma lem397720 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term947 A _8343 P _8342) = (term956 A P _8342 _8343).
Proof. exact (TRANS (@lem397685 A _8343 P _8342) (@lem397709 A P _8342 _8343)). Qed.
Lemma lem397721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem397722 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term957 A _8343 P _8342) = (term958 A P _8342 _8343).
Proof. exact (MK_COMB (@lem397721) (@lem397720 A P _8342 _8343)). Qed.
Lemma lem397736 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem397737 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term953 A _8343 P _8342) = (term954 A P _8342 _8343).
Proof. exact (@lem397736 (term554 A P _8342) (term952 A _8342 _8343)). Qed.
Lemma lem397745 {A : Type'} (P : A -> Prop) (_8343 : A) : (term955 A P _8343) = (term955 A P _8343).
Proof. exact (eq_refl (term955 A P _8343)). Qed.
Lemma lem397746 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : (term951 A _8343 P _8342) = (term956 A P _8342 _8343).
Proof. exact (MK_COMB (@lem397745 A P _8343) (@lem397737 A P _8342 _8343)). Qed.
Lemma lem397757 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : ((term947 A _8343 P _8342) = (term951 A _8343 P _8342)) = ((term956 A P _8342 _8343) = (term956 A P _8342 _8343)).
Proof. exact (MK_COMB (@lem397722 A P _8342 _8343) (@lem397746 A P _8342 _8343)). Qed.
Lemma lem397759 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem397760 (x : Prop) : (x = x) = True.
Proof. exact (@lem397759 Prop x). Qed.
Lemma lem397761 {A : Type'} (P : A -> Prop) (_8342 : A) (_8343 : A) : ((term956 A P _8342 _8343) = (term956 A P _8342 _8343)) = True.
Proof. exact (@lem397760 (term956 A P _8342 _8343)). Qed.
Lemma lem397762 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : ((term947 A _8343 P _8342) = (term951 A _8343 P _8342)) = True.
Proof. exact (TRANS (@lem397757 A P _8342 _8343) (@lem397761 A P _8342 _8343)). Qed.
Lemma lem397763 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : True = ((term947 A _8343 P _8342) = (term951 A _8343 P _8342)).
Proof. exact (SYM (@lem397762 A _8343 P _8342)). Qed.
Lemma lem397764 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term947 A _8343 P _8342) = (term951 A _8343 P _8342).
Proof. exact (EQ_MP (@lem397763 A _8343 P _8342) (@lem0)). Qed.
Lemma lem397765 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : term951 A _8343 P _8342.
Proof. exact (EQ_MP (@lem397764 A _8343 P _8342) (@lem397608 A _8343 P _8342)). Qed.
Lemma lem397767 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem397768 {A : Type'} (_8342 : A) (P : A -> Prop) (_8343 : A) : (term951 A _8343 P _8342) = (term959 A _8342 P _8343).
Proof. exact (@lem397767 (term953 A _8343 P _8342) (P _8343)). Qed.
Lemma lem397770 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem397771 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term960 A _8343 P _8342) = (term961 A _8343 P _8342).
Proof. exact (@lem397770 (term952 A _8342 _8343) (term554 A P _8342)). Qed.
Lemma lem397773 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem397774 {A : Type'} (_8342 : A) (_8343 : A) : (term962 A _8342 _8343) = (_8342 = _8343).
Proof. exact (@lem397773 (_8342 = _8343)). Qed.
Lemma lem397775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem397776 {A : Type'} (_8342 : A) (_8343 : A) : (term963 A _8342 _8343) = (term873 A _8342 _8343).
Proof. exact (MK_COMB (@lem397775) (@lem397774 A _8342 _8343)). Qed.
Lemma lem397778 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem397779 {A : Type'} (P : A -> Prop) (_8342 : A) : (term964 A P _8342) = (P _8342).
Proof. exact (@lem397778 (P _8342)). Qed.
Lemma lem397780 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term961 A _8343 P _8342) = (term965 A _8343 P _8342).
Proof. exact (MK_COMB (@lem397776 A _8342 _8343) (@lem397779 A P _8342)). Qed.
Lemma lem397781 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term960 A _8343 P _8342) = (term965 A _8343 P _8342).
Proof. exact (TRANS (@lem397771 A _8343 P _8342) (@lem397780 A _8343 P _8342)). Qed.
Lemma lem397782 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397783 {A : Type'} (_8343 : A) (P : A -> Prop) (_8342 : A) : (term966 A _8343 P _8342) = (term967 A _8343 P _8342).
Proof. exact (MK_COMB (@lem397782) (@lem397781 A _8343 P _8342)). Qed.
Lemma lem397784 {A : Type'} (P : A -> Prop) (_8343 : A) : (P _8343) = (P _8343).
Proof. exact (eq_refl (P _8343)). Qed.
Lemma lem397785 {A : Type'} (_8342 : A) (P : A -> Prop) (_8343 : A) : (term959 A _8342 P _8343) = (term968 A _8342 P _8343).
Proof. exact (MK_COMB (@lem397783 A _8343 P _8342) (@lem397784 A P _8343)). Qed.
Lemma lem397786 {A : Type'} (_8342 : A) (P : A -> Prop) (_8343 : A) : (term951 A _8343 P _8342) = (term968 A _8342 P _8343).
Proof. exact (TRANS (@lem397768 A _8342 P _8343) (@lem397785 A _8342 P _8343)). Qed.
Lemma lem397788 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) : term969 A P s x.
Proof. exact (conj (@lem397670 A x s h1) (@lem397678 A P s x h2)). Qed.
Lemma lem397790 {A : Type'} (_8342 : A) (P : A -> Prop) (_8343 : A) : term968 A _8342 P _8343.
Proof. exact (EQ_MP (@lem397786 A _8342 P _8343) (@lem397765 A _8343 P _8342)). Qed.
Lemma lem397791 {A : Type'} (_8342 : A) (P : A -> Prop) (_8343 : A) : term968 A _8342 P _8343.
Proof. exact (@lem397790 A _8342 P _8343). Qed.
Lemma lem397792 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem397791 A (term597 A s x) P x). Qed.
Lemma lem397795 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) : P x.
Proof. exact (@lem397792 A s P x (@lem397788 A P s x h1 h2)). Qed.
Lemma lem397796 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem397795 A P s x h1 h2). Qed.
Lemma lem397798 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem397799 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem397798 (P x)). Qed.
Lemma lem397800 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) : P x.
Proof. exact (EQ_MP (@lem397799 A P x) (@lem397796 A P s x h1 h2)). Qed.
Lemma lem397803 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem397805 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem397803 (P x)). Qed.
Lemma lem397808 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem397805 A P x) (@lem397592 A P x h1)). Qed.
Lemma lem397811 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (@lem397808 A P x h3 (@lem397800 A P s x h1 h2)). Qed.
Lemma lem397812 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : term180.
Proof. exact (fun h0 : ~ False => @lem397811 A s P x h1 h2 h3). Qed.
Lemma lem397814 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem397815 : term180 = False.
Proof. exact (@lem397814 False). Qed.
Lemma lem397816 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397815) (@lem397812 A s P x h1 h2 h3)). Qed.
Lemma lem397817 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h4 : term554 A P x => @lem397816 A s P x h1 h2 h3) (fun h4 : False => @lem397592 A P x h3)). Qed.
Lemma lem397818 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397817 A s P x h1 h2 h3) (@lem397592 A P x h3)). Qed.
Lemma lem397819 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h4 : term554 A P x => @lem397818 A s P x h1 h2 h3) (fun h4 : False => @lem397563 A P x h3)). Qed.
Lemma lem397820 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397819 A s P x h1 h2 h3) (@lem397563 A P x h3)). Qed.
Lemma lem397821 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h4 : term554 A P x => @lem397820 A s P x h1 h2 h3) (fun h4 : False => @lem397563 A P x h3)). Qed.
Lemma lem397822 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397821 A s P x h1 h2 h3) (@lem397563 A P x h3)). Qed.
Lemma lem397823 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h4 : term608 A s => @lem397822 A s P x h1 h2 h3) (fun h4 : False => @lem397549 A s h1)). Qed.
Lemma lem397824 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397823 A s P x h1 h2 h3) (@lem397549 A s h1)). Qed.
Lemma lem397825 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h4 : term554 A P x => @lem397824 A s P x h1 h2 h3) (fun h4 : False => @lem397521 A P x h3)). Qed.
Lemma lem397826 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397825 A s P x h1 h2 h3) (@lem397521 A P x h3)). Qed.
Lemma lem397827 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h4 : term608 A s => @lem397826 A s P x h1 h2 h3) (fun h4 : False => @lem397491 A s h1)). Qed.
Lemma lem397828 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397827 A s P x h1 h2 h3) (@lem397491 A s h1)). Qed.
Lemma lem397829 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h4 : term554 A P x => @lem397828 A s P x h1 h2 h3) (fun h4 : False => @lem397448 A P x h3)). Qed.
Lemma lem397830 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397829 A s P x h1 h2 h3) (@lem397448 A P x h3)). Qed.
Lemma lem397831 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h4 : term608 A s => @lem397830 A s P x h1 h2 h3) (fun h4 : False => @lem397422 A s h1)). Qed.
Lemma lem397832 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : False.
Proof. exact (EQ_MP (@lem397831 A s P x h1 h2 h3) (@lem397422 A s h1)). Qed.
Lemma lem397833 {A B : Type'} (something_arbitrary : B) (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : term898 A B something_arbitrary h x.
Proof. exact (fun h0 : term899 A B something_arbitrary h x => @lem397832 A s P x h1 h2 h3). Qed.
Lemma lem397834 {A B : Type'} (something_arbitrary : B) (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term791 A P s x) (h3 : term554 A P x) : something_arbitrary = (h x).
Proof. exact (EQ_MP (@lem397408 A B something_arbitrary h x) (@lem397833 A B something_arbitrary h s P x h1 h2 h3)). Qed.
Lemma lem397835 {A B : Type'} (something_arbitrary : B) (h : A -> B) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : term889 A B P s something_arbitrary h x.
Proof. exact (fun h0 : term791 A P s x => @lem397834 A B something_arbitrary h s P x h1 h0 h2). Qed.
Lemma lem397836 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (s : type1423 A) (h1 : term608 A s) : term908 A B P s something_arbitrary h x.
Proof. exact (fun h0 : term554 A P x => @lem397835 A B something_arbitrary h s P x h1 h0). Qed.
Lemma lem397837 {A B : Type'} (g : A -> A) (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (s : type1423 A) (h1 : term608 A s) : term911 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term649 A g s => @lem397836 A B P something_arbitrary h x s h1). Qed.
Lemma lem397838 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term913 A B g P s something_arbitrary h x.
Proof. exact (fun h0 : term608 A s => @lem397837 A B g P something_arbitrary h x s h0). Qed.
Lemma lem397843 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term917 A B P s something_arbitrary h x.
Proof. exact (fun g : A -> A => @lem397838 A B g P s something_arbitrary h x). Qed.
Lemma lem397848 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term921 A B s something_arbitrary h x.
Proof. exact (fun P : A -> Prop => @lem397843 A B P s something_arbitrary h x). Qed.
Lemma lem397853 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : term925 A B something_arbitrary h x.
Proof. exact (fun s : type1423 A => @lem397848 A B s something_arbitrary h x). Qed.
Lemma lem397858 {A B : Type'} (h : A -> B) (x : A) : term929 A B h x.
Proof. exact (fun something_arbitrary : B => @lem397853 A B something_arbitrary h x). Qed.
Lemma lem397863 {A B : Type'} (x : A) : term933 A B x.
Proof. exact (fun h : A -> B => @lem397858 A B h x). Qed.
Lemma lem397868 {A B : Type'} : term937 A B.
Proof. exact (fun x : A => @lem397863 A B x). Qed.
Lemma lem397869 {A B : Type'} : term936 A B.
Proof. exact (EQ_MP (@lem397400 A B) (@lem397868 A B)). Qed.
Lemma lem397870 {A B : Type'} (x : A) : term973 A B x.
Proof. exact (@lem397869 A B x). Qed.
Lemma lem397871 {A B : Type'} (x : A) : (term973 A B x) = (term932 A B x).
Proof. exact (eq_refl (term973 A B x)). Qed.
Lemma lem397872 {A B : Type'} (x : A) : term932 A B x.
Proof. exact (EQ_MP (@lem397871 A B x) (@lem397870 A B x)). Qed.
Lemma lem397873 {A B : Type'} (x : A) (h : A -> B) : term974 A B x h.
Proof. exact (@lem397872 A B x h). Qed.
Lemma lem397874 {A B : Type'} (h : A -> B) (x : A) : (term974 A B x h) = (term928 A B h x).
Proof. exact (eq_refl (term974 A B x h)). Qed.
Lemma lem397875 {A B : Type'} (h : A -> B) (x : A) : term928 A B h x.
Proof. exact (EQ_MP (@lem397874 A B h x) (@lem397873 A B x h)). Qed.
Lemma lem397876 {A B : Type'} (h : A -> B) (x : A) (something_arbitrary : B) : term975 A B h x something_arbitrary.
Proof. exact (@lem397875 A B h x something_arbitrary). Qed.
Lemma lem397877 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : (term975 A B h x something_arbitrary) = (term924 A B something_arbitrary h x).
Proof. exact (eq_refl (term975 A B h x something_arbitrary)). Qed.
Lemma lem397878 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) : term924 A B something_arbitrary h x.
Proof. exact (EQ_MP (@lem397877 A B something_arbitrary h x) (@lem397876 A B h x something_arbitrary)). Qed.
Lemma lem397879 {A B : Type'} (something_arbitrary : B) (h : A -> B) (x : A) (s : type1423 A) : term976 A B something_arbitrary h x s.
Proof. exact (@lem397878 A B something_arbitrary h x s). Qed.
Lemma lem397880 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term976 A B something_arbitrary h x s) = (term920 A B s something_arbitrary h x).
Proof. exact (eq_refl (term976 A B something_arbitrary h x s)). Qed.
Lemma lem397881 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term920 A B s something_arbitrary h x.
Proof. exact (EQ_MP (@lem397880 A B s something_arbitrary h x) (@lem397879 A B something_arbitrary h x s)). Qed.
Lemma lem397882 {A B : Type'} (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (P : A -> Prop) : term977 A B s something_arbitrary h x P.
Proof. exact (@lem397881 A B s something_arbitrary h x P). Qed.
Lemma lem397883 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term977 A B s something_arbitrary h x P) = (term916 A B P s something_arbitrary h x).
Proof. exact (eq_refl (term977 A B s something_arbitrary h x P)). Qed.
Lemma lem397884 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term916 A B P s something_arbitrary h x.
Proof. exact (EQ_MP (@lem397883 A B P s something_arbitrary h x) (@lem397882 A B s something_arbitrary h x P)). Qed.
Lemma lem397885 {A B : Type'} (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) : term978 A B P s something_arbitrary h x g.
Proof. exact (@lem397884 A B P s something_arbitrary h x g). Qed.
Lemma lem397886 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : (term978 A B P s something_arbitrary h x g) = (term900 A B g P s something_arbitrary h x).
Proof. exact (eq_refl (term978 A B P s something_arbitrary h x g)). Qed.
Lemma lem397887 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term900 A B g P s something_arbitrary h x.
Proof. exact (EQ_MP (@lem397886 A B g P s something_arbitrary h x) (@lem397885 A B P s something_arbitrary h x g)). Qed.
Lemma lem397889 {A B : Type'} (g : A -> A) (P : A -> Prop) (s : type1423 A) (something_arbitrary : B) (h : A -> B) (x : A) : term900 A B g P s something_arbitrary h x.
Proof. exact (@lem397158 A B g P s something_arbitrary h x (@lem397887 A B g P s something_arbitrary h x)). Qed.
Lemma lem397890 {A B : Type'} (g : A -> A) (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (s : type1423 A) (h1 : term608 A s) : term910 A B g P s something_arbitrary h x.
Proof. exact (@lem397889 A B g P s something_arbitrary h x (@lem394512 A s h1)). Qed.
Lemma lem397891 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : term907 A B P s something_arbitrary h x.
Proof. exact (@lem397890 A B g P something_arbitrary h x s h1 (@lem394513 A g s h2)). Qed.
Lemma lem397892 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term905 A B P s something_arbitrary h x.
Proof. exact (@lem397891 A B P something_arbitrary h x g s h1 h2 (@lem394333 A P x h3)). Qed.
Lemma lem397893 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) : term898 A B something_arbitrary h x.
Proof. exact (@lem397892 A B something_arbitrary h g s P x h1 h2 h4 (@lem397121 A P s x h3)). Qed.
Lemma lem397894 {A B : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) (h5 : term899 A B something_arbitrary h x) : False.
Proof. exact (@lem397893 A B something_arbitrary h g s P x h1 h2 h3 h4 (@lem397142 A B something_arbitrary h x h5)). Qed.
Lemma lem397895 {A B : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) (h5 : term899 A B something_arbitrary h x) : (term899 A B something_arbitrary h x) = False.
Proof. exact (prop_ext (fun h6 : term899 A B something_arbitrary h x => @lem397894 A B g s P something_arbitrary h x h1 h2 h3 h4 h5) (fun h6 : False => @lem397142 A B something_arbitrary h x h5)). Qed.
Lemma lem397896 {A B : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) (h5 : term899 A B something_arbitrary h x) : False.
Proof. exact (EQ_MP (@lem397895 A B g s P something_arbitrary h x h1 h2 h3 h4 h5) (@lem397142 A B something_arbitrary h x h5)). Qed.
Lemma lem397897 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) : term898 A B something_arbitrary h x.
Proof. exact (fun h0 : term899 A B something_arbitrary h x => @lem397896 A B g s P something_arbitrary h x h1 h2 h3 h4 h0). Qed.
Lemma lem397899 {A B : Type'} (h : A -> B) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem397901 {A : Type'} (P : A -> Prop) (x : A) : term548 A P x.
Proof. exact (EQ_MP (@lem394317 A P x) (@lem394316 A P x)). Qed.
Lemma lem397902 {A : Type'} (P : A -> Prop) (x : A) : term548 A P x.
Proof. exact (@lem397901 A P x). Qed.
Lemma lem397903 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term979 A P s x.
Proof. exact (@lem397902 A (term879 A P s x) x). Qed.
Lemma lem397911 {A B : Type'} (f : A -> B) (y : A) : (term615 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem397912 {A : Type'} (f : A -> Prop) (y : A) : (term980 A f y) = (f y).
Proof. exact (@lem397911 A Prop f y). Qed.
Lemma lem397913 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (y : A) : (term981 A P s x y) = (term982 A P s x y).
Proof. exact (@lem397912 A (term879 A P s x) y). Qed.
Lemma lem397914 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term982 A P s x y) = (term870 A y P s x).
Proof. exact (eq_refl (term982 A P s x y)). Qed.
Lemma lem397915 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term983 A P s x) = (term879 A P s x).
Proof. exact (fun_ext (fun y : A => @lem397914 A y P s x)). Qed.
Lemma lem397916 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem397917 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (y : A) : (term981 A P s x y) = (term982 A P s x y).
Proof. exact (MK_COMB (@lem397915 A P s x) (@lem397916 A y)). Qed.
Lemma lem397918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem397919 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (y : A) : (term984 A P s x y) = (term985 A P s x y).
Proof. exact (MK_COMB (@lem397918) (@lem397917 A P s x y)). Qed.
Lemma lem397920 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term982 A P s x y) = (term870 A y P s x).
Proof. exact (eq_refl (term982 A P s x y)). Qed.
Lemma lem397921 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : ((term981 A P s x y) = (term982 A P s x y)) = ((term982 A P s x y) = (term870 A y P s x)).
Proof. exact (MK_COMB (@lem397919 A P s x y) (@lem397920 A y P s x)). Qed.
Lemma lem397922 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term982 A P s x y) = (term870 A y P s x).
Proof. exact (EQ_MP (@lem397921 A y P s x) (@lem397913 A P s x y)). Qed.
Lemma lem397939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem397940 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term985 A P s x y) = (term986 A y P s x).
Proof. exact (MK_COMB (@lem397939) (@lem397922 A y P s x)). Qed.
Lemma lem397943 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem397944 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : ((term982 A P s x y) = (y = x)) = ((term870 A y P s x) = (y = x)).
Proof. exact (MK_COMB (@lem397940 A y P s x) (@lem397943 A y x)). Qed.
Lemma lem397947 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term987 A P s x) = (term988 A P s x).
Proof. exact (fun_ext (fun y : A => @lem397944 A P s y x)). Qed.
Lemma lem397948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem397949 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term989 A P s x) = (term990 A P s x).
Proof. exact (MK_COMB (@lem397948 A) (@lem397947 A P s x)). Qed.
Lemma lem397954 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term990 A P s x) = (term989 A P s x).
Proof. exact (SYM (@lem397949 A P s x)). Qed.
Lemma lem397956 {A : Type'} (P : A -> Prop) (Q : Prop) : (term542 A P Q) = (term543 A P Q).
Proof. exact (EQ_MP (@lem394294 A P Q) (@lem394293 A P Q)). Qed.
Lemma lem397957 (P : nat -> Prop) (Q : Prop) : (term991 P Q) = (term992 P Q).
Proof. exact (@lem397956 nat P Q). Qed.
Lemma lem397958 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term993 A P s y x) = (term994 A P s y x).
Proof. exact (@lem397957 (term854 A y P s x) (y = x)). Qed.
Lemma lem397959 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term866 A y P s x n) = (term867 A y n P s x).
Proof. exact (eq_refl (term866 A y P s x n)). Qed.
Lemma lem397960 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term868 A y P s x) = (term854 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem397959 A y n P s x)). Qed.
Lemma lem397961 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem397962 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term869 A y P s x) = (term870 A y P s x).
Proof. exact (MK_COMB (@lem397961) (@lem397960 A y P s x)). Qed.
Lemma lem397963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397964 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term995 A y P s x) = (term996 A y P s x).
Proof. exact (MK_COMB (@lem397963) (@lem397962 A y P s x)). Qed.
Lemma lem397965 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem397966 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term993 A P s y x) = (term997 A P s y x).
Proof. exact (MK_COMB (@lem397964 A y P s x) (@lem397965 A y x)). Qed.
Lemma lem397967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem397968 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term998 A P s y x) = (term999 A P s y x).
Proof. exact (MK_COMB (@lem397967) (@lem397966 A P s y x)). Qed.
Lemma lem397969 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term866 A y P s x n) = (term867 A y n P s x).
Proof. exact (eq_refl (term866 A y P s x n)). Qed.
Lemma lem397970 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem397971 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1000 A y P s x n) = (term1001 A y n P s x).
Proof. exact (MK_COMB (@lem397970) (@lem397969 A y n P s x)). Qed.
Lemma lem397972 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem397973 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term1002 A P s n y x) = (term1003 A n P s y x).
Proof. exact (MK_COMB (@lem397971 A y n P s x) (@lem397972 A y x)). Qed.
Lemma lem397974 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term1004 A P s y x) = (term1005 A P s y x).
Proof. exact (fun_ext (fun n : nat => @lem397973 A n P s y x)). Qed.
Lemma lem397975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem397976 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term994 A P s y x) = (term1006 A P s y x).
Proof. exact (MK_COMB (@lem397975) (@lem397974 A P s y x)). Qed.
Lemma lem397977 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : ((term993 A P s y x) = (term994 A P s y x)) = ((term997 A P s y x) = (term1006 A P s y x)).
Proof. exact (MK_COMB (@lem397968 A P s y x) (@lem397976 A P s y x)). Qed.
Lemma lem397978 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term997 A P s y x) = (term1006 A P s y x).
Proof. exact (EQ_MP (@lem397977 A P s y x) (@lem397958 A P s y x)). Qed.
Lemma lem397986 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1007 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem397987 (p : Prop) (q : Prop) (p' : Prop) : term1008 p q p'.
Proof. exact (fun q' : Prop => @lem397986 p q p' q'). Qed.
Lemma lem397988 (p : Prop) (q : Prop) : term1009 p q.
Proof. exact (fun p' : Prop => @lem397987 p q p'). Qed.
Lemma lem397989 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : term1010 A n P s y x.
Proof. exact (@lem397988 (term867 A y n P s x) (y = x)). Qed.
Lemma lem397990 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) : term1011 A n P s y x p'.
Proof. exact (@lem397989 A n P s y x p'). Qed.
Lemma lem397991 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) : (term1011 A n P s y x p') = (term1012 A n P s y x p').
Proof. exact (eq_refl (term1011 A n P s y x p')). Qed.
Lemma lem397992 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) : term1012 A n P s y x p'.
Proof. exact (EQ_MP (@lem397991 A n P s y x p') (@lem397990 A n P s y x p')). Qed.
Lemma lem397993 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) (q' : Prop) : term1013 A n P s y x p' q'.
Proof. exact (@lem397992 A n P s y x p' q'). Qed.
Lemma lem397994 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) (q' : Prop) : (term1013 A n P s y x p' q') = (term1014 A n P s y x p' q').
Proof. exact (eq_refl (term1013 A n P s y x p' q')). Qed.
Lemma lem397995 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (y : A) (x : A) (p' : Prop) (q' : Prop) : term1014 A n P s y x p' q'.
Proof. exact (EQ_MP (@lem397994 A n P s y x p' q') (@lem397993 A n P s y x p' q')). Qed.
Lemma lem398029 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term867 A y n P s x) = (term867 A y n P s x).
Proof. exact (eq_refl (term867 A y n P s x)). Qed.
Lemma lem398030 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (q' : Prop) : term1015 A y n P s x q'.
Proof. exact (@lem397995 A n P s y x (term867 A y n P s x) q'). Qed.
Lemma lem398031 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (q' : Prop) : term1016 A y n P s x q'.
Proof. exact (@lem398030 A y n P s x q' (@lem398029 A y n P s x)). Qed.
Lemma lem398032 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term867 A y n P s x) : term867 A y n P s x.
Proof. exact (h1). Qed.
Lemma lem398054 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term867 A y n P s x) : y = (s x n).
Proof. exact (proj1 (@lem398032 A y n P s x h1)). Qed.
Lemma lem398055 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem398056 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term867 A y n P s x) : (@eq A y) = (term1017 A s x n).
Proof. exact (MK_COMB (@lem398055 A) (@lem398054 A y n P s x h1)). Qed.
Lemma lem398057 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem398058 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term867 A y n P s x) : (y = x) = ((s x n) = x).
Proof. exact (MK_COMB (@lem398056 A y n P s x h1) (@lem398057 A x)). Qed.
Lemma lem398061 {A : Type'} (P : A -> Prop) (y : A) (s : type1423 A) (n : nat) (x : A) : term1018 A P y s n x.
Proof. exact (fun h0 : term867 A y n P s x => @lem398058 A y n P s x h0). Qed.
Lemma lem398062 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1019 A y P s n x.
Proof. exact (@lem398031 A y n P s x ((s x n) = x)). Qed.
Lemma lem398063 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1003 A n P s y x) = (term1020 A y P s n x).
Proof. exact (@lem398062 A y P s n x (@lem398061 A P y s n x)). Qed.
Lemma lem398173 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1005 A P s y x) = (term1021 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem398063 A y P s n x)). Qed.
Lemma lem398283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398284 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1006 A P s y x) = (term1022 A y P s x).
Proof. exact (MK_COMB (@lem398283) (@lem398173 A y P s x)). Qed.
Lemma lem398398 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term997 A P s y x) = (term1022 A y P s x).
Proof. exact (TRANS (@lem397978 A P s y x) (@lem398284 A y P s x)). Qed.
Lemma lem398399 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term1022 A y P s x) = (term997 A P s y x).
Proof. exact (SYM (@lem398398 A y P s x)). Qed.
Lemma lem398401 (P : nat -> Prop) : term242 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem398402 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1023 A y P s x.
Proof. exact (@lem398401 (term1021 A y P s x)). Qed.
Lemma lem398403 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1024 A y P s x) = (term1025 A y P s x).
Proof. exact (eq_refl (term1024 A y P s x)). Qed.
Lemma lem398404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem398405 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1026 A y P s x) = (term1027 A y P s x).
Proof. exact (MK_COMB (@lem398404) (@lem398403 A y P s x)). Qed.
Lemma lem398406 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1028 A y P s x n) = (term1020 A y P s n x).
Proof. exact (eq_refl (term1028 A y P s x n)). Qed.
Lemma lem398407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398408 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1029 A y P s x n) = (term1030 A y P s n x).
Proof. exact (MK_COMB (@lem398407) (@lem398406 A y P s n x)). Qed.
Lemma lem398409 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1031 A y P s x n) = (term1032 A y P s n x).
Proof. exact (eq_refl (term1031 A y P s x n)). Qed.
Lemma lem398410 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1033 A y P s x n) = (term1034 A y P s n x).
Proof. exact (MK_COMB (@lem398408 A y P s n x) (@lem398409 A y P s n x)). Qed.
Lemma lem398411 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1035 A y P s x) = (term1036 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem398410 A y P s n x)). Qed.
Lemma lem398412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398413 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1037 A y P s x) = (term1038 A y P s x).
Proof. exact (MK_COMB (@lem398412) (@lem398411 A y P s x)). Qed.
Lemma lem398414 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1039 A y P s x) = (term1040 A y P s x).
Proof. exact (MK_COMB (@lem398405 A y P s x) (@lem398413 A y P s x)). Qed.
Lemma lem398415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398416 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1041 A y P s x) = (term1042 A y P s x).
Proof. exact (MK_COMB (@lem398415) (@lem398414 A y P s x)). Qed.
Lemma lem398417 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1028 A y P s x n) = (term1020 A y P s n x).
Proof. exact (eq_refl (term1028 A y P s x n)). Qed.
Lemma lem398418 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1043 A y P s x) = (term1021 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem398417 A y P s n x)). Qed.
Lemma lem398419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398420 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1044 A y P s x) = (term1022 A y P s x).
Proof. exact (MK_COMB (@lem398419) (@lem398418 A y P s x)). Qed.
Lemma lem398421 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1023 A y P s x) = (term1045 A y P s x).
Proof. exact (MK_COMB (@lem398416 A y P s x) (@lem398420 A y P s x)). Qed.
Lemma lem398422 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1045 A y P s x.
Proof. exact (EQ_MP (@lem398421 A y P s x) (@lem398402 A y P s x)). Qed.
Lemma lem398423 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1020 A y P s n x) : term1020 A y P s n x.
Proof. exact (h1). Qed.
Lemma lem398424 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term596 A s x.
Proof. exact (@lem394512 A s h1 x). Qed.
Lemma lem398425 {A : Type'} (s : type1423 A) (x : A) : (term596 A s x) = ((term597 A s x) = x).
Proof. exact (eq_refl (term596 A s x)). Qed.
Lemma lem398433 {A : Type'} (P : A -> Prop) (x : A) : term751 A P x.
Proof. exact (@lem82 (P x)). Qed.
Lemma lem398444 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem398425 A s x) (@lem398424 A x s h1)). Qed.
Lemma lem398445 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem398444 A x s h1). Qed.
Lemma lem398446 {A : Type'} (y : A) : (@eq A y) = (@eq A y).
Proof. exact (eq_refl (@eq A y)). Qed.
Lemma lem398447 {A : Type'} (y : A) (x : A) (s : type1423 A) (h1 : term608 A s) : (y = (term597 A s x)) = (y = x).
Proof. exact (MK_COMB (@lem398446 A y) (@lem398445 A x s h1)). Qed.
Lemma lem398450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem398451 {A : Type'} (y : A) (x : A) (s : type1423 A) (h1 : term608 A s) : (term872 A y s x) = (term873 A y x).
Proof. exact (MK_COMB (@lem398450) (@lem398447 A y x s h1)). Qed.
Lemma lem398455 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem398425 A s x) (@lem398424 A x s h1)). Qed.
Lemma lem398456 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem398455 A x s h1). Qed.
Lemma lem398457 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem398458 {A : Type'} (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : (term784 A P s x) = (P x).
Proof. exact (MK_COMB (@lem398457 A P) (@lem398456 A x s h1)). Qed.
Lemma lem398460 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : (P x) = False.
Proof. exact (@lem398433 A P x (@lem394333 A P x h1)). Qed.
Lemma lem398461 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term784 A P s x) = False.
Proof. exact (TRANS (@lem398458 A P x s h1) (@lem398460 A P x h2)). Qed.
Lemma lem398462 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem398463 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term768 A P s x) = (~ False).
Proof. exact (MK_COMB (@lem398462) (@lem398461 A s P x h1 h2)). Qed.
Lemma lem398465 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem398466 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term768 A P s x) = True.
Proof. exact (TRANS (@lem398463 A s P x h1 h2) (@lem398465)). Qed.
Lemma lem398467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem398468 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term874 A P s x) = (and True).
Proof. exact (MK_COMB (@lem398467) (@lem398466 A s P x h1 h2)). Qed.
Lemma lem398475 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term875 A P s x) = (term875 A P s x).
Proof. exact (eq_refl (term875 A P s x)). Qed.
Lemma lem398476 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term876 A P s x) = (term1046 A P s x).
Proof. exact (MK_COMB (@lem398468 A s P x h1 h2) (@lem398475 A P s x)). Qed.
Lemma lem398478 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem398479 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1046 A P s x) = (term875 A P s x).
Proof. exact (@lem398478 (term875 A P s x)). Qed.
Lemma lem398486 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term876 A P s x) = (term875 A P s x).
Proof. exact (TRANS (@lem398476 A s P x h1 h2) (@lem398479 A P s x)). Qed.
Lemma lem398487 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term856 A y P s x) = (term1047 A y P s x).
Proof. exact (MK_COMB (@lem398451 A y x s h1) (@lem398486 A s P x h1 h2)). Qed.
Lemma lem398490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398491 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term1048 A y P s x) = (term1049 A y P s x).
Proof. exact (MK_COMB (@lem398490) (@lem398487 A y s P x h1 h2)). Qed.
Lemma lem398495 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem398425 A s x) (@lem398424 A x s h1)). Qed.
Lemma lem398496 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem398495 A x s h1). Qed.
Lemma lem398497 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem398498 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term1050 A s x) = (@eq A x).
Proof. exact (MK_COMB (@lem398497 A) (@lem398496 A x s h1)). Qed.
Lemma lem398499 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem398500 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : ((term597 A s x) = x) = (x = x).
Proof. exact (MK_COMB (@lem398498 A x s h1) (@lem398499 A x)). Qed.
Lemma lem398502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem398503 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem398502 A x). Qed.
Lemma lem398504 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : ((term597 A s x) = x) = True.
Proof. exact (TRANS (@lem398500 A x s h1) (@lem398503 A x)). Qed.
Lemma lem398505 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term1025 A y P s x) = (term1051 A y P s x).
Proof. exact (MK_COMB (@lem398491 A y s P x h1 h2) (@lem398504 A x s h1)). Qed.
Lemma lem398507 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem398508 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1051 A y P s x) = True.
Proof. exact (@lem398507 (term1047 A y P s x)). Qed.
Lemma lem398509 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : (term1025 A y P s x) = True.
Proof. exact (TRANS (@lem398505 A y s P x h1 h2) (@lem398508 A y P s x)). Qed.
Lemma lem398510 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : True = (term1025 A y P s x).
Proof. exact (SYM (@lem398509 A y s P x h1 h2)). Qed.
Lemma lem398511 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : term1025 A y P s x.
Proof. exact (EQ_MP (@lem398510 A y s P x h1 h2) (@lem0)). Qed.
Lemma lem398546 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem398547 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1032 A y P s n x) = (term1052 A y P s n x).
Proof. exact (@lem398546 (term1032 A y P s n x)). Qed.
Lemma lem398548 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1052 A y P s n x) = (term1032 A y P s n x).
Proof. exact (SYM (@lem398547 A y P s n x)). Qed.
Lemma lem398549 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1053 A y P s n x.
Proof. exact (h1). Qed.
Lemma lem398552 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1054 A g y P s n x) : term1054 A g y P s n x.
Proof. exact (h1). Qed.
Lemma lem398553 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1055 A g y P s n x.
Proof. exact (fun h0 : term1054 A g y P s n x => @lem398552 A g y P s n x h0). Qed.
Lemma lem398554 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1055 A g y P s n x) : term1055 A g y P s n x.
Proof. exact (h1). Qed.
Lemma lem398555 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1054 A g y P s n x) : term1054 A g y P s n x.
Proof. exact (h1). Qed.
Lemma lem398556 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1054 A g y P s n x) (h2 : term1055 A g y P s n x) : term1054 A g y P s n x.
Proof. exact (@lem398554 A g y P s n x h2 (@lem398555 A g y P s n x h1)). Qed.
Lemma lem398557 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1054 A g y P s n x) : term1056 A g y P s n x.
Proof. exact (fun h0 : term1055 A g y P s n x => @lem398556 A g y P s n x h1 h0). Qed.
Lemma lem398558 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1055 A g y P s n x) : term1055 A g y P s n x.
Proof. exact (h1). Qed.
Lemma lem398559 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1054 A g y P s n x) (h2 : term1055 A g y P s n x) : term1054 A g y P s n x.
Proof. exact (@lem398557 A g y P s n x h1 (@lem398558 A g y P s n x h2)). Qed.
Lemma lem398560 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1055 A g y P s n x) : term1055 A g y P s n x.
Proof. exact (fun h0 : term1054 A g y P s n x => @lem398559 A g y P s n x h0 h1). Qed.
Lemma lem398561 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1057 A g y P s n x.
Proof. exact (fun h0 : term1055 A g y P s n x => @lem398560 A g y P s n x h0). Qed.
Lemma lem398564 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1055 A g y P s n x.
Proof. exact (@lem398561 A g y P s n x (@lem398553 A g y P s n x)). Qed.
Lemma lem398565 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1055 A g y P s n x.
Proof. exact (@lem398564 A g y P s n x). Qed.
Lemma lem398643 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem398644 : term1058 = term1059.
Proof. exact (@lem398643 term327). Qed.
Lemma lem398649 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1060 A y P s n x) = (term1060 A y P s n x).
Proof. exact (eq_refl (term1060 A y P s n x)). Qed.
Lemma lem398650 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1061 A y P s n x) = (term1062 A y P s n x).
Proof. exact (MK_COMB (@lem398649 A y P s n x) (@lem398644)). Qed.
Lemma lem398653 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1030 A y P s n x) = (term1030 A y P s n x).
Proof. exact (eq_refl (term1030 A y P s n x)). Qed.
Lemma lem398654 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1063 A y P s n x) = (term1064 A y P s n x).
Proof. exact (MK_COMB (@lem398653 A y P s n x) (@lem398650 A y P s n x)). Qed.
Lemma lem398657 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (eq_refl (term807 A P s x)). Qed.
Lemma lem398658 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1065 A y P s n x) = (term1066 A y P s n x).
Proof. exact (MK_COMB (@lem398657 A P s x) (@lem398654 A y P s n x)). Qed.
Lemma lem398661 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem398662 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1067 A y P s n x) = (term1068 A y P s n x).
Proof. exact (MK_COMB (@lem398661 A P x) (@lem398658 A y P s n x)). Qed.
Lemma lem398665 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (eq_refl (term909 A g s)). Qed.
Lemma lem398666 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1069 A g y P s n x) = (term1070 A g y P s n x).
Proof. exact (MK_COMB (@lem398665 A g s) (@lem398662 A y P s n x)). Qed.
Lemma lem398669 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (eq_refl (term912 A s)). Qed.
Lemma lem398670 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1054 A g y P s n x) = (term1071 A g y P s n x).
Proof. exact (MK_COMB (@lem398669 A s) (@lem398666 A g y P s n x)). Qed.
Lemma lem398673 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1072 A y P s n x) = (term1073 A y P s n x).
Proof. exact (fun_ext (fun g : A -> A => @lem398670 A g y P s n x)). Qed.
Lemma lem398674 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem398675 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1074 A y P s n x) = (term1075 A y P s n x).
Proof. exact (MK_COMB (@lem398674 A) (@lem398673 A y P s n x)). Qed.
Lemma lem398680 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1076 A P s n x) = (term1077 A P s n x).
Proof. exact (fun_ext (fun y : A => @lem398675 A y P s n x)). Qed.
Lemma lem398681 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398682 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1078 A P s n x) = (term1079 A P s n x).
Proof. exact (MK_COMB (@lem398681 A) (@lem398680 A P s n x)). Qed.
Lemma lem398687 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1080 A s n x) = (term1081 A s n x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem398682 A P s n x)). Qed.
Lemma lem398688 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem398689 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1082 A s n x) = (term1083 A s n x).
Proof. exact (MK_COMB (@lem398688 A) (@lem398687 A s n x)). Qed.
Lemma lem398694 {A : Type'} (n : nat) (x : A) : (term1084 A n x) = (term1085 A n x).
Proof. exact (fun_ext (fun s : type1423 A => @lem398689 A s n x)). Qed.
Lemma lem398695 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem398696 {A : Type'} (n : nat) (x : A) : (term1086 A n x) = (term1087 A n x).
Proof. exact (MK_COMB (@lem398695 A) (@lem398694 A n x)). Qed.
Lemma lem398701 {A : Type'} (x : A) : (term1088 A x) = (term1089 A x).
Proof. exact (fun_ext (fun n : nat => @lem398696 A n x)). Qed.
Lemma lem398702 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398703 {A : Type'} (x : A) : (term1090 A x) = (term1091 A x).
Proof. exact (MK_COMB (@lem398702) (@lem398701 A x)). Qed.
Lemma lem398708 {A : Type'} : (term1092 A) = (term1093 A).
Proof. exact (fun_ext (fun x : A => @lem398703 A x)). Qed.
Lemma lem398709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398718 {A : Type'} : (term1094 A) = (term1095 A).
Proof. exact (MK_COMB (@lem398709 A) (@lem398708 A)). Qed.
Lemma lem398719 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem398720 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem398719 n)). Qed.
Lemma lem398721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398722 : term327 = term327.
Proof. exact (MK_COMB (@lem398721) (@lem398720)). Qed.
Lemma lem398723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem398724 : term1059 = term1059.
Proof. exact (MK_COMB (@lem398723) (@lem398722)). Qed.
Lemma lem398725 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((term635 A s x n) = x) = ((term635 A s x n) = x).
Proof. exact (eq_refl ((term635 A s x n) = x)). Qed.
Lemma lem398730 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term843 A n P s x m) = (term843 A n P s x m).
Proof. exact (eq_refl (term843 A n P s x m)). Qed.
Lemma lem398731 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term845 A n P s x) = (term845 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem398730 A n P s x m)). Qed.
Lemma lem398732 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398733 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term847 A n P s x) = (term847 A n P s x).
Proof. exact (MK_COMB (@lem398732) (@lem398731 A n P s x)). Qed.
Lemma lem398738 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term723 A P s x n) = (term723 A P s x n).
Proof. exact (eq_refl (term723 A P s x n)). Qed.
Lemma lem398739 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term849 A n P s x) = (term849 A n P s x).
Proof. exact (MK_COMB (@lem398738 A P s x n) (@lem398733 A n P s x)). Qed.
Lemma lem398742 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term721 A y s x n) = (term721 A y s x n).
Proof. exact (eq_refl (term721 A y s x n)). Qed.
Lemma lem398743 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term850 A y n P s x) = (term850 A y n P s x).
Proof. exact (MK_COMB (@lem398742 A y s x n) (@lem398739 A n P s x)). Qed.
Lemma lem398744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398745 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1096 A y n P s x) = (term1096 A y n P s x).
Proof. exact (MK_COMB (@lem398744) (@lem398743 A y n P s x)). Qed.
Lemma lem398746 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1032 A y P s n x) = (term1032 A y P s n x).
Proof. exact (MK_COMB (@lem398745 A y n P s x) (@lem398725 A s n x)). Qed.
Lemma lem398747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem398748 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1053 A y P s n x) = (term1053 A y P s n x).
Proof. exact (MK_COMB (@lem398747) (@lem398746 A y P s n x)). Qed.
Lemma lem398749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398750 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1060 A y P s n x) = (term1060 A y P s n x).
Proof. exact (MK_COMB (@lem398749) (@lem398748 A y P s n x)). Qed.
Lemma lem398751 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1062 A y P s n x) = (term1062 A y P s n x).
Proof. exact (MK_COMB (@lem398750 A y P s n x) (@lem398724)). Qed.
Lemma lem398752 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((s x n) = x) = ((s x n) = x).
Proof. exact (eq_refl ((s x n) = x)). Qed.
Lemma lem398757 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1097 A n P s x m) = (term1097 A n P s x m).
Proof. exact (eq_refl (term1097 A n P s x m)). Qed.
Lemma lem398758 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1098 A n P s x) = (term1098 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem398757 A n P s x m)). Qed.
Lemma lem398759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398760 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1099 A n P s x) = (term1099 A n P s x).
Proof. exact (MK_COMB (@lem398759) (@lem398758 A n P s x)). Qed.
Lemma lem398765 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1100 A P s x n) = (term1100 A P s x n).
Proof. exact (eq_refl (term1100 A P s x n)). Qed.
Lemma lem398766 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1101 A n P s x) = (term1101 A n P s x).
Proof. exact (MK_COMB (@lem398765 A P s x n) (@lem398760 A n P s x)). Qed.
Lemma lem398769 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1102 A y s x n) = (term1102 A y s x n).
Proof. exact (eq_refl (term1102 A y s x n)). Qed.
Lemma lem398770 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term867 A y n P s x) = (term867 A y n P s x).
Proof. exact (MK_COMB (@lem398769 A y s x n) (@lem398766 A n P s x)). Qed.
Lemma lem398771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398772 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1001 A y n P s x) = (term1001 A y n P s x).
Proof. exact (MK_COMB (@lem398771) (@lem398770 A y n P s x)). Qed.
Lemma lem398773 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1020 A y P s n x) = (term1020 A y P s n x).
Proof. exact (MK_COMB (@lem398772 A y n P s x) (@lem398752 A s n x)). Qed.
Lemma lem398774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398775 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1030 A y P s n x) = (term1030 A y P s n x).
Proof. exact (MK_COMB (@lem398774) (@lem398773 A y P s n x)). Qed.
Lemma lem398776 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1064 A y P s n x) = (term1064 A y P s n x).
Proof. exact (MK_COMB (@lem398775 A y P s n x) (@lem398751 A y P s n x)). Qed.
Lemma lem398779 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term779 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term779 A P s x n)). Qed.
Lemma lem398780 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term766 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem398779 A P s x n)). Qed.
Lemma lem398781 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem398782 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem398781) (@lem398780 A P s x)). Qed.
Lemma lem398783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398784 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (MK_COMB (@lem398783) (@lem398782 A P s x)). Qed.
Lemma lem398785 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1066 A y P s n x) = (term1066 A y P s n x).
Proof. exact (MK_COMB (@lem398784 A P s x) (@lem398776 A y P s n x)). Qed.
Lemma lem398790 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem398791 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1068 A y P s n x) = (term1068 A y P s n x).
Proof. exact (MK_COMB (@lem398790 A P x) (@lem398785 A y P s n x)). Qed.
Lemma lem398792 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : ((term687 A s g x n) = (term635 A s x n)) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl ((term687 A s g x n) = (term635 A s x n))). Qed.
Lemma lem398793 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term938 A g s n) = (term938 A g s n).
Proof. exact (fun_ext (fun x : A => @lem398792 A g s x n)). Qed.
Lemma lem398794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398795 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term657 A g s n) = (term657 A g s n).
Proof. exact (MK_COMB (@lem398794 A) (@lem398793 A g s n)). Qed.
Lemma lem398796 {A : Type'} (g : A -> A) (s : type1423 A) : (term651 A g s) = (term651 A g s).
Proof. exact (fun_ext (fun n : nat => @lem398795 A g s n)). Qed.
Lemma lem398797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398798 {A : Type'} (g : A -> A) (s : type1423 A) : (term649 A g s) = (term649 A g s).
Proof. exact (MK_COMB (@lem398797) (@lem398796 A g s)). Qed.
Lemma lem398799 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398800 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (MK_COMB (@lem398799) (@lem398798 A g s)). Qed.
Lemma lem398801 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1070 A g y P s n x) = (term1070 A g y P s n x).
Proof. exact (MK_COMB (@lem398800 A g s) (@lem398791 A y P s n x)). Qed.
Lemma lem398802 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem398803 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem398802 A s x)). Qed.
Lemma lem398804 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398805 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem398804 A) (@lem398803 A s)). Qed.
Lemma lem398806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem398807 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (MK_COMB (@lem398806) (@lem398805 A s)). Qed.
Lemma lem398808 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1071 A g y P s n x) = (term1071 A g y P s n x).
Proof. exact (MK_COMB (@lem398807 A s) (@lem398801 A g y P s n x)). Qed.
Lemma lem398809 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1073 A y P s n x) = (term1073 A y P s n x).
Proof. exact (fun_ext (fun g : A -> A => @lem398808 A g y P s n x)). Qed.
Lemma lem398810 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem398811 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1075 A y P s n x) = (term1075 A y P s n x).
Proof. exact (MK_COMB (@lem398810 A) (@lem398809 A y P s n x)). Qed.
Lemma lem398812 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1077 A P s n x) = (term1077 A P s n x).
Proof. exact (fun_ext (fun y : A => @lem398811 A y P s n x)). Qed.
Lemma lem398813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398814 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1079 A P s n x) = (term1079 A P s n x).
Proof. exact (MK_COMB (@lem398813 A) (@lem398812 A P s n x)). Qed.
Lemma lem398815 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1081 A s n x) = (term1081 A s n x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem398814 A P s n x)). Qed.
Lemma lem398816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem398817 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1083 A s n x) = (term1083 A s n x).
Proof. exact (MK_COMB (@lem398816 A) (@lem398815 A s n x)). Qed.
Lemma lem398818 {A : Type'} (n : nat) (x : A) : (term1085 A n x) = (term1085 A n x).
Proof. exact (fun_ext (fun s : type1423 A => @lem398817 A s n x)). Qed.
Lemma lem398819 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem398820 {A : Type'} (n : nat) (x : A) : (term1087 A n x) = (term1087 A n x).
Proof. exact (MK_COMB (@lem398819 A) (@lem398818 A n x)). Qed.
Lemma lem398821 {A : Type'} (x : A) : (term1089 A x) = (term1089 A x).
Proof. exact (fun_ext (fun n : nat => @lem398820 A n x)). Qed.
Lemma lem398822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem398823 {A : Type'} (x : A) : (term1091 A x) = (term1091 A x).
Proof. exact (MK_COMB (@lem398822) (@lem398821 A x)). Qed.
Lemma lem398824 {A : Type'} : (term1093 A) = (term1093 A).
Proof. exact (fun_ext (fun x : A => @lem398823 A x)). Qed.
Lemma lem398825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398826 {A : Type'} : (term1095 A) = (term1095 A).
Proof. exact (MK_COMB (@lem398825 A) (@lem398824 A)). Qed.
Lemma lem398935 {A : Type'} : (term1094 A) = (term1095 A).
Proof. exact (TRANS (@lem398718 A) (@lem398826 A)). Qed.
Lemma lem398936 {A : Type'} : (term1095 A) = (term1094 A).
Proof. exact (SYM (@lem398935 A)). Qed.
Lemma lem398937 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (h1). Qed.
Lemma lem398940 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (h1). Qed.
Lemma lem398941 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1020 A y P s n x) : term1020 A y P s n x.
Proof. exact (h1). Qed.
Lemma lem398942 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1053 A y P s n x.
Proof. exact (h1). Qed.
Lemma lem398943 (h1 : term327) : term327.
Proof. exact (h1). Qed.
Lemma lem398944 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem398945 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem398944 A s x)). Qed.
Lemma lem398946 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem398955 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem398946 A) (@lem398945 A s)). Qed.
Lemma lem398956 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem398955 A s) (@lem398937 A s h1)). Qed.
Lemma lem398982 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem398983 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term779 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term779 A P s x n)). Qed.
Lemma lem398984 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term766 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem398983 A P s x n)). Qed.
Lemma lem398985 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem398994 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem398985) (@lem398984 A P s x)). Qed.
Lemma lem398995 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (EQ_MP (@lem398994 A P s x) (@lem398940 A P s x h1)). Qed.
Lemma lem398999 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term939 A P s x n) = (term841 A P s x n).
Proof. exact (@lem16933 (term841 A P s x n)). Qed.
Lemma lem399006 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1103 A n P s x m) = (term1104 A n P s x m).
Proof. exact (@lem17362 (Peano.lt m n) (term841 A P s x m)). Qed.
Lemma lem399007 (P : nat -> Prop) : (term1105 P) = (term1106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem399008 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1107 A n P s x) = (term1108 A n P s x).
Proof. exact (@lem399007 (term1098 A n P s x)). Qed.
Lemma lem399009 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1109 A n P s x m) = (term1097 A n P s x m).
Proof. exact (eq_refl (term1109 A n P s x m)). Qed.
Lemma lem399010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem399011 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1110 A n P s x m) = (term1103 A n P s x m).
Proof. exact (MK_COMB (@lem399010) (@lem399009 A n P s x m)). Qed.
Lemma lem399012 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1110 A n P s x m) = (term1104 A n P s x m).
Proof. exact (TRANS (@lem399011 A n P s x m) (@lem399006 A n P s x m)). Qed.
Lemma lem399013 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1111 A n P s x) = (term1112 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399012 A n P s x m)). Qed.
Lemma lem399014 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399015 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1108 A n P s x) = (term1113 A n P s x).
Proof. exact (MK_COMB (@lem399014) (@lem399013 A n P s x)). Qed.
Lemma lem399016 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1107 A n P s x) = (term1113 A n P s x).
Proof. exact (TRANS (@lem399008 A n P s x) (@lem399015 A n P s x)). Qed.
Lemma lem399017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem399018 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1114 A P s x n) = (term1115 A P s x n).
Proof. exact (MK_COMB (@lem399017) (@lem398999 A P s x n)). Qed.
Lemma lem399019 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1116 A n P s x) = (term1117 A n P s x).
Proof. exact (MK_COMB (@lem399018 A P s x n) (@lem399016 A n P s x)). Qed.
Lemma lem399020 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1118 A n P s x) = (term1116 A n P s x).
Proof. exact (@lem17045 (term779 A P s x n) (term1099 A n P s x)). Qed.
Lemma lem399021 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1118 A n P s x) = (term1117 A n P s x).
Proof. exact (TRANS (@lem399020 A n P s x) (@lem399019 A n P s x)). Qed.
Lemma lem399023 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem399024 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1120 A y n P s x) = (term1121 A y n P s x).
Proof. exact (MK_COMB (@lem399023 A y s x n) (@lem399021 A n P s x)). Qed.
Lemma lem399025 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1122 A y n P s x) = (term1120 A y n P s x).
Proof. exact (@lem17045 (y = (s x n)) (term1101 A n P s x)). Qed.
Lemma lem399026 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1122 A y n P s x) = (term1121 A y n P s x).
Proof. exact (TRANS (@lem399025 A y n P s x) (@lem399024 A y n P s x)). Qed.
Lemma lem399027 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((s x n) = x) = ((s x n) = x).
Proof. exact (eq_refl ((s x n) = x)). Qed.
Lemma lem399028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem399029 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1123 A y n P s x) = (term1124 A y n P s x).
Proof. exact (MK_COMB (@lem399028) (@lem399026 A y n P s x)). Qed.
Lemma lem399030 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1125 A y P s n x) = (term1126 A y P s n x).
Proof. exact (MK_COMB (@lem399029 A y n P s x) (@lem399027 A s n x)). Qed.
Lemma lem399031 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1020 A y P s n x) = (term1125 A y P s n x).
Proof. exact (@lem17265 (term867 A y n P s x) ((s x n) = x)). Qed.
Lemma lem399032 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1020 A y P s n x) = (term1126 A y P s n x).
Proof. exact (TRANS (@lem399031 A y P s n x) (@lem399030 A y P s n x)). Qed.
Lemma lem399083 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem399084 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem399083 nat P Q). Qed.
Lemma lem399085 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1127 A n P s x) = (term1128 A n P s x).
Proof. exact (@lem399084 (term841 A P s x n) (term1112 A n P s x)). Qed.
Lemma lem399086 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1129 A n P s x m) = (term1104 A n P s x m).
Proof. exact (eq_refl (term1129 A n P s x m)). Qed.
Lemma lem399087 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1130 A n P s x) = (term1112 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399086 A n P s x m)). Qed.
Lemma lem399088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399089 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1131 A n P s x) = (term1113 A n P s x).
Proof. exact (MK_COMB (@lem399088) (@lem399087 A n P s x)). Qed.
Lemma lem399090 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1115 A P s x n) = (term1115 A P s x n).
Proof. exact (eq_refl (term1115 A P s x n)). Qed.
Lemma lem399091 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1127 A n P s x) = (term1117 A n P s x).
Proof. exact (MK_COMB (@lem399090 A P s x n) (@lem399089 A n P s x)). Qed.
Lemma lem399092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem399093 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1132 A n P s x) = (term1133 A n P s x).
Proof. exact (MK_COMB (@lem399092) (@lem399091 A n P s x)). Qed.
Lemma lem399094 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1129 A n P s x m) = (term1104 A n P s x m).
Proof. exact (eq_refl (term1129 A n P s x m)). Qed.
Lemma lem399095 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1115 A P s x n) = (term1115 A P s x n).
Proof. exact (eq_refl (term1115 A P s x n)). Qed.
Lemma lem399096 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1134 A n P s x m) = (term1135 A n P s x m).
Proof. exact (MK_COMB (@lem399095 A P s x n) (@lem399094 A n P s x m)). Qed.
Lemma lem399097 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1136 A n P s x) = (term1137 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399096 A n P s x m)). Qed.
Lemma lem399098 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399099 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1128 A n P s x) = (term1138 A n P s x).
Proof. exact (MK_COMB (@lem399098) (@lem399097 A n P s x)). Qed.
Lemma lem399100 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1127 A n P s x) = (term1128 A n P s x)) = ((term1117 A n P s x) = (term1138 A n P s x)).
Proof. exact (MK_COMB (@lem399093 A n P s x) (@lem399099 A n P s x)). Qed.
Lemma lem399101 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1117 A n P s x) = (term1138 A n P s x).
Proof. exact (EQ_MP (@lem399100 A n P s x) (@lem399085 A n P s x)). Qed.
Lemma lem399102 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem399103 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1121 A y n P s x) = (term1139 A y n P s x).
Proof. exact (MK_COMB (@lem399102 A y s x n) (@lem399101 A n P s x)). Qed.
Lemma lem399105 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem399106 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem399105 nat P Q). Qed.
Lemma lem399107 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1140 A y n P s x) = (term1141 A y n P s x).
Proof. exact (@lem399106 (term1142 A y s x n) (term1137 A n P s x)). Qed.
Lemma lem399108 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1143 A n P s x m) = (term1135 A n P s x m).
Proof. exact (eq_refl (term1143 A n P s x m)). Qed.
Lemma lem399109 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1144 A n P s x) = (term1137 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399108 A n P s x m)). Qed.
Lemma lem399110 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399111 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1145 A n P s x) = (term1138 A n P s x).
Proof. exact (MK_COMB (@lem399110) (@lem399109 A n P s x)). Qed.
Lemma lem399112 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem399113 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1140 A y n P s x) = (term1139 A y n P s x).
Proof. exact (MK_COMB (@lem399112 A y s x n) (@lem399111 A n P s x)). Qed.
Lemma lem399114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem399115 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1146 A y n P s x) = (term1147 A y n P s x).
Proof. exact (MK_COMB (@lem399114) (@lem399113 A y n P s x)). Qed.
Lemma lem399116 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1143 A n P s x m) = (term1135 A n P s x m).
Proof. exact (eq_refl (term1143 A n P s x m)). Qed.
Lemma lem399117 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem399118 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1148 A y n P s x m) = (term1149 A y n P s x m).
Proof. exact (MK_COMB (@lem399117 A y s x n) (@lem399116 A n P s x m)). Qed.
Lemma lem399119 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1150 A y n P s x) = (term1151 A y n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399118 A y n P s x m)). Qed.
Lemma lem399120 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399121 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1141 A y n P s x) = (term1152 A y n P s x).
Proof. exact (MK_COMB (@lem399120) (@lem399119 A y n P s x)). Qed.
Lemma lem399122 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1140 A y n P s x) = (term1141 A y n P s x)) = ((term1139 A y n P s x) = (term1152 A y n P s x)).
Proof. exact (MK_COMB (@lem399115 A y n P s x) (@lem399121 A y n P s x)). Qed.
Lemma lem399123 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1139 A y n P s x) = (term1152 A y n P s x).
Proof. exact (EQ_MP (@lem399122 A y n P s x) (@lem399107 A y n P s x)). Qed.
Lemma lem399124 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1121 A y n P s x) = (term1152 A y n P s x).
Proof. exact (TRANS (@lem399103 A y n P s x) (@lem399123 A y n P s x)). Qed.
Lemma lem399125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem399126 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1124 A y n P s x) = (term1153 A y n P s x).
Proof. exact (MK_COMB (@lem399125) (@lem399124 A y n P s x)). Qed.
Lemma lem399127 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((s x n) = x) = ((s x n) = x).
Proof. exact (eq_refl ((s x n) = x)). Qed.
Lemma lem399128 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1126 A y P s n x) = (term1154 A y P s n x).
Proof. exact (MK_COMB (@lem399126 A y n P s x) (@lem399127 A s n x)). Qed.
Lemma lem399130 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1155 A P Q) = (term1156 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem399131 (P : nat -> Prop) (Q : Prop) : (term1157 P Q) = (term1158 P Q).
Proof. exact (@lem399130 nat P Q). Qed.
Lemma lem399132 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1159 A y P s n x) = (term1160 A y P s n x).
Proof. exact (@lem399131 (term1151 A y n P s x) ((s x n) = x)). Qed.
Lemma lem399133 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1161 A y n P s x m) = (term1149 A y n P s x m).
Proof. exact (eq_refl (term1161 A y n P s x m)). Qed.
Lemma lem399134 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1162 A y n P s x) = (term1151 A y n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399133 A y n P s x m)). Qed.
Lemma lem399135 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399136 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1163 A y n P s x) = (term1152 A y n P s x).
Proof. exact (MK_COMB (@lem399135) (@lem399134 A y n P s x)). Qed.
Lemma lem399137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem399138 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1164 A y n P s x) = (term1153 A y n P s x).
Proof. exact (MK_COMB (@lem399137) (@lem399136 A y n P s x)). Qed.
Lemma lem399139 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((s x n) = x) = ((s x n) = x).
Proof. exact (eq_refl ((s x n) = x)). Qed.
Lemma lem399140 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1159 A y P s n x) = (term1154 A y P s n x).
Proof. exact (MK_COMB (@lem399138 A y n P s x) (@lem399139 A s n x)). Qed.
Lemma lem399141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem399142 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1165 A y P s n x) = (term1166 A y P s n x).
Proof. exact (MK_COMB (@lem399141) (@lem399140 A y P s n x)). Qed.
Lemma lem399143 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1161 A y n P s x m) = (term1149 A y n P s x m).
Proof. exact (eq_refl (term1161 A y n P s x m)). Qed.
Lemma lem399144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem399145 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1167 A y n P s x m) = (term1168 A y n P s x m).
Proof. exact (MK_COMB (@lem399144) (@lem399143 A y n P s x m)). Qed.
Lemma lem399146 {A : Type'} (s : type1423 A) (n : nat) (x : A) : ((s x n) = x) = ((s x n) = x).
Proof. exact (eq_refl ((s x n) = x)). Qed.
Lemma lem399147 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) : (term1169 A y P m s n x) = (term1170 A y P m s n x).
Proof. exact (MK_COMB (@lem399145 A y n P s x m) (@lem399146 A s n x)). Qed.
Lemma lem399148 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1171 A y P s n x) = (term1172 A y P s n x).
Proof. exact (fun_ext (fun m : nat => @lem399147 A y P m s n x)). Qed.
Lemma lem399149 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem399150 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1160 A y P s n x) = (term1173 A y P s n x).
Proof. exact (MK_COMB (@lem399149) (@lem399148 A y P s n x)). Qed.
Lemma lem399151 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : ((term1159 A y P s n x) = (term1160 A y P s n x)) = ((term1154 A y P s n x) = (term1173 A y P s n x)).
Proof. exact (MK_COMB (@lem399142 A y P s n x) (@lem399150 A y P s n x)). Qed.
Lemma lem399152 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1154 A y P s n x) = (term1173 A y P s n x).
Proof. exact (EQ_MP (@lem399151 A y P s n x) (@lem399132 A y P s n x)). Qed.
Lemma lem399154 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1126 A y P s n x) = (term1173 A y P s n x).
Proof. exact (TRANS (@lem399128 A y P s n x) (@lem399152 A y P s n x)). Qed.
Lemma lem399155 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1020 A y P s n x) = (term1173 A y P s n x).
Proof. exact (TRANS (@lem399032 A y P s n x) (@lem399154 A y P s n x)). Qed.
Lemma lem399156 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1020 A y P s n x) : term1173 A y P s n x.
Proof. exact (EQ_MP (@lem399155 A y P s n x) (@lem398941 A y P s n x h1)). Qed.
Lemma lem399165 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term843 A n P s x m) = (term1174 A n P s x m).
Proof. exact (@lem17265 (term363 m n) (term841 A P s x m)). Qed.
Lemma lem399166 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term845 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399165 A n P s x m)). Qed.
Lemma lem399167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399168 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term847 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399167) (@lem399166 A n P s x)). Qed.
Lemma lem399170 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term723 A P s x n) = (term723 A P s x n).
Proof. exact (eq_refl (term723 A P s x n)). Qed.
Lemma lem399171 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term849 A n P s x) = (term1177 A n P s x).
Proof. exact (MK_COMB (@lem399170 A P s x n) (@lem399168 A n P s x)). Qed.
Lemma lem399173 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term721 A y s x n) = (term721 A y s x n).
Proof. exact (eq_refl (term721 A y s x n)). Qed.
Lemma lem399174 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term850 A y n P s x) = (term1178 A y n P s x).
Proof. exact (MK_COMB (@lem399173 A y s x n) (@lem399171 A n P s x)). Qed.
Lemma lem399175 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1179 A s n x) = (term1179 A s n x).
Proof. exact (eq_refl (term1179 A s n x)). Qed.
Lemma lem399176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem399177 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1180 A y n P s x) = (term1181 A y n P s x).
Proof. exact (MK_COMB (@lem399176) (@lem399174 A y n P s x)). Qed.
Lemma lem399178 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1182 A y P s n x) = (term1183 A y P s n x).
Proof. exact (MK_COMB (@lem399177 A y n P s x) (@lem399175 A s n x)). Qed.
Lemma lem399179 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1053 A y P s n x) = (term1182 A y P s n x).
Proof. exact (@lem17362 (term850 A y n P s x) ((term635 A s x n) = x)). Qed.
Lemma lem399232 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1053 A y P s n x) = (term1183 A y P s n x).
Proof. exact (TRANS (@lem399179 A y P s n x) (@lem399178 A y P s n x)). Qed.
Lemma lem399233 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1183 A y P s n x.
Proof. exact (EQ_MP (@lem399232 A y P s n x) (@lem398942 A y P s n x h1)). Qed.
Lemma lem399234 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399235 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399234 n)). Qed.
Lemma lem399236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399245 : term327 = term327.
Proof. exact (MK_COMB (@lem399236) (@lem399235)). Qed.
Lemma lem399246 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399245) (@lem398943 h1)). Qed.
Lemma lem399259 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem399260 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem399259 A s x)). Qed.
Lemma lem399261 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem399262 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem399261 A) (@lem399260 A s)). Qed.
Lemma lem399263 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem399262 A s) (@lem398956 A s h1)). Qed.
Lemma lem399293 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399306 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1179 A s n x) = (term1179 A s n x).
Proof. exact (eq_refl (term1179 A s n x)). Qed.
Lemma lem399325 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1174 A n P s x m) = (term1174 A n P s x m).
Proof. exact (eq_refl (term1174 A n P s x m)). Qed.
Lemma lem399326 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1175 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399325 A n P s x m)). Qed.
Lemma lem399327 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399328 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1176 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399327) (@lem399326 A n P s x)). Qed.
Lemma lem399341 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term723 A P s x n) = (term723 A P s x n).
Proof. exact (eq_refl (term723 A P s x n)). Qed.
Lemma lem399342 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1177 A n P s x) = (term1177 A n P s x).
Proof. exact (MK_COMB (@lem399341 A P s x n) (@lem399328 A n P s x)). Qed.
Lemma lem399355 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term721 A y s x n) = (term721 A y s x n).
Proof. exact (eq_refl (term721 A y s x n)). Qed.
Lemma lem399356 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1178 A y n P s x) = (term1178 A y n P s x).
Proof. exact (MK_COMB (@lem399355 A y s x n) (@lem399342 A n P s x)). Qed.
Lemma lem399357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem399358 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1181 A y n P s x) = (term1181 A y n P s x).
Proof. exact (MK_COMB (@lem399357) (@lem399356 A y n P s x)). Qed.
Lemma lem399359 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1183 A y P s n x) = (term1183 A y P s n x).
Proof. exact (MK_COMB (@lem399358 A y n P s x) (@lem399306 A s n x)). Qed.
Lemma lem399360 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1183 A y P s n x.
Proof. exact (EQ_MP (@lem399359 A y P s n x) (@lem399233 A y P s n x h1)). Qed.
Lemma lem399369 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399370 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399369 n)). Qed.
Lemma lem399371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399372 : term327 = term327.
Proof. exact (MK_COMB (@lem399371) (@lem399370)). Qed.
Lemma lem399373 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399372) (@lem399246 h1)). Qed.
Lemma lem399427 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term1170 A y P m s n x) : term1170 A y P m s n x.
Proof. exact (h1). Qed.
Lemma lem399439 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1178 A y n P s x.
Proof. exact (proj1 (@lem399360 A y P s n x h1)). Qed.
Lemma lem399440 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1177 A n P s x.
Proof. exact (proj2 (@lem399439 A y P s n x h1)). Qed.
Lemma lem399442 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1176 A n P s x.
Proof. exact (proj2 (@lem399440 A y P s n x h1)). Qed.
Lemma lem399444 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) (h1 : term1149 A y n P s x m) : term1149 A y n P s x m.
Proof. exact (h1). Qed.
Lemma lem399447 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) (h1 : term1135 A n P s x m) : term1135 A n P s x m.
Proof. exact (h1). Qed.
Lemma lem399453 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem399454 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem399453 A s x)). Qed.
Lemma lem399455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem399457 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem399455 A) (@lem399454 A s)). Qed.
Lemma lem399458 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem399457 A s) (@lem399263 A s h1)). Qed.
Lemma lem399472 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399474 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399475 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399474 n)). Qed.
Lemma lem399476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399478 : term327 = term327.
Proof. exact (MK_COMB (@lem399476) (@lem399475)). Qed.
Lemma lem399479 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399478) (@lem399373 h1)). Qed.
Lemma lem399503 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1174 A n P s x m) = (term1174 A n P s x m).
Proof. exact (eq_refl (term1174 A n P s x m)). Qed.
Lemma lem399504 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1175 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399503 A n P s x m)). Qed.
Lemma lem399505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399507 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1176 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399505) (@lem399504 A n P s x)). Qed.
Lemma lem399508 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1176 A n P s x.
Proof. exact (EQ_MP (@lem399507 A n P s x) (@lem399442 A y P s n x h1)). Qed.
Lemma lem399514 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem399515 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem399514 A s x)). Qed.
Lemma lem399516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem399518 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem399516 A) (@lem399515 A s)). Qed.
Lemma lem399519 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem399518 A s) (@lem399263 A s h1)). Qed.
Lemma lem399533 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399535 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399536 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399535 n)). Qed.
Lemma lem399537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399539 : term327 = term327.
Proof. exact (MK_COMB (@lem399537) (@lem399536)). Qed.
Lemma lem399540 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399539) (@lem399373 h1)). Qed.
Lemma lem399564 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1174 A n P s x m) = (term1174 A n P s x m).
Proof. exact (eq_refl (term1174 A n P s x m)). Qed.
Lemma lem399565 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1175 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399564 A n P s x m)). Qed.
Lemma lem399566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399568 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1176 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399566) (@lem399565 A n P s x)). Qed.
Lemma lem399569 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1176 A n P s x.
Proof. exact (EQ_MP (@lem399568 A n P s x) (@lem399442 A y P s n x h1)). Qed.
Lemma lem399575 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem399576 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem399575 A s x)). Qed.
Lemma lem399577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem399579 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem399577 A) (@lem399576 A s)). Qed.
Lemma lem399580 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem399579 A s) (@lem399263 A s h1)). Qed.
Lemma lem399594 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399596 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399597 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399596 n)). Qed.
Lemma lem399598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399600 : term327 = term327.
Proof. exact (MK_COMB (@lem399598) (@lem399597)). Qed.
Lemma lem399601 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399600) (@lem399373 h1)). Qed.
Lemma lem399625 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1174 A n P s x m) = (term1174 A n P s x m).
Proof. exact (eq_refl (term1174 A n P s x m)). Qed.
Lemma lem399626 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1175 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399625 A n P s x m)). Qed.
Lemma lem399627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399629 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1176 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399627) (@lem399626 A n P s x)). Qed.
Lemma lem399630 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1176 A n P s x.
Proof. exact (EQ_MP (@lem399629 A n P s x) (@lem399442 A y P s n x h1)). Qed.
Lemma lem399640 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem399641 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem399640 A s x)). Qed.
Lemma lem399642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem399644 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem399642 A) (@lem399641 A s)). Qed.
Lemma lem399645 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem399644 A s) (@lem399263 A s h1)). Qed.
Lemma lem399659 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399661 (n : nat) : (term325 n) = (term325 n).
Proof. exact (eq_refl (term325 n)). Qed.
Lemma lem399662 : term326 = term326.
Proof. exact (fun_ext (fun n : nat => @lem399661 n)). Qed.
Lemma lem399663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399665 : term327 = term327.
Proof. exact (MK_COMB (@lem399663) (@lem399662)). Qed.
Lemma lem399666 (h1 : term327) : term327.
Proof. exact (EQ_MP (@lem399665) (@lem399373 h1)). Qed.
Lemma lem399690 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1174 A n P s x m) = (term1174 A n P s x m).
Proof. exact (eq_refl (term1174 A n P s x m)). Qed.
Lemma lem399691 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1175 A n P s x) = (term1175 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem399690 A n P s x m)). Qed.
Lemma lem399692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem399694 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1176 A n P s x) = (term1176 A n P s x).
Proof. exact (MK_COMB (@lem399692) (@lem399691 A n P s x)). Qed.
Lemma lem399695 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1176 A n P s x.
Proof. exact (EQ_MP (@lem399694 A n P s x) (@lem399442 A y P s n x h1)). Qed.
Lemma lem399700 {A : Type'} (_8356 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8356.
Proof. exact (@lem399458 A s h1 _8356). Qed.
Lemma lem399701 {A : Type'} (s : type1423 A) (_8356 : A) : (term596 A s _8356) = ((term597 A s _8356) = _8356).
Proof. exact (eq_refl (term596 A s _8356)). Qed.
Lemma lem399709 (_8359 : nat) (h1 : term327) : term1184 _8359.
Proof. exact (@lem399479 h1 _8359). Qed.
Lemma lem399710 (_8359 : nat) : (term1184 _8359) = (term325 _8359).
Proof. exact (eq_refl (term1184 _8359)). Qed.
Lemma lem399712 {A : Type'} (_8360 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1185 A n P s x _8360.
Proof. exact (@lem399508 A y P s n x h1 _8360). Qed.
Lemma lem399713 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) : (term1185 A n P s x _8360) = (term1174 A n P s x _8360).
Proof. exact (eq_refl (term1185 A n P s x _8360)). Qed.
Lemma lem399715 {A : Type'} (_8361 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8361.
Proof. exact (@lem399519 A s h1 _8361). Qed.
Lemma lem399716 {A : Type'} (s : type1423 A) (_8361 : A) : (term596 A s _8361) = ((term597 A s _8361) = _8361).
Proof. exact (eq_refl (term596 A s _8361)). Qed.
Lemma lem399724 (_8364 : nat) (h1 : term327) : term1184 _8364.
Proof. exact (@lem399540 h1 _8364). Qed.
Lemma lem399725 (_8364 : nat) : (term1184 _8364) = (term325 _8364).
Proof. exact (eq_refl (term1184 _8364)). Qed.
Lemma lem399727 {A : Type'} (_8365 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1185 A n P s x _8365.
Proof. exact (@lem399569 A y P s n x h1 _8365). Qed.
Lemma lem399728 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) : (term1185 A n P s x _8365) = (term1174 A n P s x _8365).
Proof. exact (eq_refl (term1185 A n P s x _8365)). Qed.
Lemma lem399730 {A : Type'} (_8366 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8366.
Proof. exact (@lem399580 A s h1 _8366). Qed.
Lemma lem399731 {A : Type'} (s : type1423 A) (_8366 : A) : (term596 A s _8366) = ((term597 A s _8366) = _8366).
Proof. exact (eq_refl (term596 A s _8366)). Qed.
Lemma lem399739 (_8369 : nat) (h1 : term327) : term1184 _8369.
Proof. exact (@lem399601 h1 _8369). Qed.
Lemma lem399740 (_8369 : nat) : (term1184 _8369) = (term325 _8369).
Proof. exact (eq_refl (term1184 _8369)). Qed.
Lemma lem399742 {A : Type'} (_8370 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1185 A n P s x _8370.
Proof. exact (@lem399630 A y P s n x h1 _8370). Qed.
Lemma lem399743 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) : (term1185 A n P s x _8370) = (term1174 A n P s x _8370).
Proof. exact (eq_refl (term1185 A n P s x _8370)). Qed.
Lemma lem399745 {A : Type'} (_8371 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8371.
Proof. exact (@lem399645 A s h1 _8371). Qed.
Lemma lem399746 {A : Type'} (s : type1423 A) (_8371 : A) : (term596 A s _8371) = ((term597 A s _8371) = _8371).
Proof. exact (eq_refl (term596 A s _8371)). Qed.
Lemma lem399754 (_8374 : nat) (h1 : term327) : term1184 _8374.
Proof. exact (@lem399666 h1 _8374). Qed.
Lemma lem399755 (_8374 : nat) : (term1184 _8374) = (term325 _8374).
Proof. exact (eq_refl (term1184 _8374)). Qed.
Lemma lem399757 {A : Type'} (_8375 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1185 A n P s x _8375.
Proof. exact (@lem399695 A y P s n x h1 _8375). Qed.
Lemma lem399758 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) : (term1185 A n P s x _8375) = (term1174 A n P s x _8375).
Proof. exact (eq_refl (term1185 A n P s x _8375)). Qed.
Lemma lem399765 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399789 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399813 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399839 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399913 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem399983 {A : Type'} (_8360 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1174 A n P s x _8360.
Proof. exact (EQ_MP (@lem399713 A n P s x _8360) (@lem399712 A _8360 y P s n x h1)). Qed.
Lemma lem400052 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem400122 {A : Type'} (_8365 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1174 A n P s x _8365.
Proof. exact (EQ_MP (@lem399728 A n P s x _8365) (@lem399727 A _8365 y P s n x h1)). Qed.
Lemma lem400192 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem400262 {A : Type'} (_8370 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1174 A n P s x _8370.
Proof. exact (EQ_MP (@lem399743 A n P s x _8370) (@lem399742 A _8370 y P s n x h1)). Qed.
Lemma lem400346 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem400416 {A : Type'} (_8375 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1174 A n P s x _8375.
Proof. exact (EQ_MP (@lem399758 A n P s x _8375) (@lem399757 A _8375 y P s n x h1)). Qed.
Lemma lem400450 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem400451 {A : Type'} (_8462 : A) (_8463 : A) (h1 : _8462 = _8463) : _8462 = _8463.
Proof. exact (h1). Qed.
Lemma lem400452 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) (h1 : _8462 = _8463) : (P _8462) = (P _8463).
Proof. exact (MK_COMB (@lem400450 A P) (@lem400451 A _8462 _8463 h1)). Qed.
Lemma lem400454 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem400455 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : term944 A _8463 P _8462.
Proof. exact (@lem400454 (P _8463) (P _8462)). Qed.
Lemma lem400456 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) (h1 : _8462 = _8463) : term945 A _8463 P _8462.
Proof. exact (@lem400455 A _8463 P _8462 (@lem400452 A P _8462 _8463 h1)). Qed.
Lemma lem400457 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : term946 A _8463 P _8462.
Proof. exact (fun h0 : _8462 = _8463 => @lem400456 A P _8462 _8463 h0). Qed.
Lemma lem400459 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem400460 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term946 A _8463 P _8462) = (term947 A _8463 P _8462).
Proof. exact (@lem400459 (_8462 = _8463) (term945 A _8463 P _8462)). Qed.
Lemma lem400461 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : term947 A _8463 P _8462.
Proof. exact (EQ_MP (@lem400460 A _8463 P _8462) (@lem400457 A _8463 P _8462)). Qed.
Lemma lem400506 {A : Type'} (_8356 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8356) = _8356.
Proof. exact (EQ_MP (@lem399701 A s _8356) (@lem399700 A _8356 s h1)). Qed.
Lemma lem400507 {A : Type'} (_8356 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8356) = _8356.
Proof. exact (@lem400506 A _8356 s h1). Qed.
Lemma lem400508 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem400507 A x s h1). Qed.
Lemma lem400509 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem400508 A x s h1). Qed.
Lemma lem400511 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400512 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem400511 ((term597 A s x) = x)). Qed.
Lemma lem400513 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem400512 A s x) (@lem400509 A x s h1)). Qed.
Lemma lem400515 (_8359 : nat) (h1 : term327) : term325 _8359.
Proof. exact (EQ_MP (@lem399710 _8359) (@lem399709 _8359 h1)). Qed.
Lemma lem400516 (n : nat) (h1 : term327) : term325 n.
Proof. exact (@lem400515 n h1). Qed.
Lemma lem400517 (n : nat) (h1 : term327) : term1186 n.
Proof. exact (fun h0 : term1187 n => @lem400516 n h1). Qed.
Lemma lem400519 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400520 (n : nat) : (term1186 n) = (term325 n).
Proof. exact (@lem400519 (term325 n)). Qed.
Lemma lem400521 (n : nat) (h1 : term327) : term325 n.
Proof. exact (EQ_MP (@lem400520 n) (@lem400517 n h1)). Qed.
Lemma lem400527 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400528 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : (term1174 A n P s x _8360) = (term1188 A P s x _8360 n).
Proof. exact (@lem400527 (term841 A P s x _8360) (term439 _8360 n)). Qed.
Lemma lem400534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem400535 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : (term1189 A n P s x _8360) = (term1190 A P s x _8360 n).
Proof. exact (MK_COMB (@lem400534) (@lem400528 A P s x _8360 n)). Qed.
Lemma lem400541 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : (term1188 A P s x _8360 n) = (term1188 A P s x _8360 n).
Proof. exact (eq_refl (term1188 A P s x _8360 n)). Qed.
Lemma lem400542 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : ((term1174 A n P s x _8360) = (term1188 A P s x _8360 n)) = ((term1188 A P s x _8360 n) = (term1188 A P s x _8360 n)).
Proof. exact (MK_COMB (@lem400535 A P s x _8360 n) (@lem400541 A P s x _8360 n)). Qed.
Lemma lem400544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem400545 (x : Prop) : (x = x) = True.
Proof. exact (@lem400544 Prop x). Qed.
Lemma lem400546 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : ((term1188 A P s x _8360 n) = (term1188 A P s x _8360 n)) = True.
Proof. exact (@lem400545 (term1188 A P s x _8360 n)). Qed.
Lemma lem400547 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : ((term1174 A n P s x _8360) = (term1188 A P s x _8360 n)) = True.
Proof. exact (TRANS (@lem400542 A P s x _8360 n) (@lem400546 A P s x _8360 n)). Qed.
Lemma lem400548 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : True = ((term1174 A n P s x _8360) = (term1188 A P s x _8360 n)).
Proof. exact (SYM (@lem400547 A P s x _8360 n)). Qed.
Lemma lem400549 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) (n : nat) : (term1174 A n P s x _8360) = (term1188 A P s x _8360 n).
Proof. exact (EQ_MP (@lem400548 A P s x _8360 n) (@lem0)). Qed.
Lemma lem400550 {A : Type'} (_8360 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1188 A P s x _8360 n.
Proof. exact (EQ_MP (@lem400549 A P s x _8360 n) (@lem399983 A _8360 y P s n x h1)). Qed.
Lemma lem400552 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem400553 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) : (term1188 A P s x _8360 n) = (term1191 A n P s x _8360).
Proof. exact (@lem400552 (term439 _8360 n) (term841 A P s x _8360)). Qed.
Lemma lem400555 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400556 (_8360 : nat) (n : nat) : (term483 _8360 n) = (term363 _8360 n).
Proof. exact (@lem400555 (term363 _8360 n)). Qed.
Lemma lem400557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem400558 (_8360 : nat) (n : nat) : (term484 _8360 n) = (term485 _8360 n).
Proof. exact (MK_COMB (@lem400557) (@lem400556 _8360 n)). Qed.
Lemma lem400559 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) : (term841 A P s x _8360) = (term841 A P s x _8360).
Proof. exact (eq_refl (term841 A P s x _8360)). Qed.
Lemma lem400560 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) : (term1191 A n P s x _8360) = (term843 A n P s x _8360).
Proof. exact (MK_COMB (@lem400558 _8360 n) (@lem400559 A P s x _8360)). Qed.
Lemma lem400561 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8360 : nat) : (term1188 A P s x _8360 n) = (term843 A n P s x _8360).
Proof. exact (TRANS (@lem400553 A n P s x _8360) (@lem400560 A n P s x _8360)). Qed.
Lemma lem400564 {A : Type'} (_8360 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term843 A n P s x _8360.
Proof. exact (EQ_MP (@lem400561 A n P s x _8360) (@lem400550 A _8360 y P s n x h1)). Qed.
Lemma lem400565 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1192 A n P s x.
Proof. exact (@lem400564 A (NUMERAL 0) y P s n x h1). Qed.
Lemma lem400568 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (@lem400565 A y P s n x h2 (@lem400521 n h1)). Qed.
Lemma lem400569 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem400568 A y P s n x h1 h2). Qed.
Lemma lem400571 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400572 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem400571 (term784 A P s x)). Qed.
Lemma lem400573 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (EQ_MP (@lem400572 A P s x) (@lem400569 A y P s n x h1 h2)). Qed.
Lemma lem400579 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem400580 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term947 A _8463 P _8462) = (term951 A _8463 P _8462).
Proof. exact (@lem400579 (P _8463) (term952 A _8462 _8463) (term554 A P _8462)). Qed.
Lemma lem400594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400595 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term953 A _8463 P _8462) = (term954 A P _8462 _8463).
Proof. exact (@lem400594 (term554 A P _8462) (term952 A _8462 _8463)). Qed.
Lemma lem400603 {A : Type'} (P : A -> Prop) (_8463 : A) : (term955 A P _8463) = (term955 A P _8463).
Proof. exact (eq_refl (term955 A P _8463)). Qed.
Lemma lem400604 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term951 A _8463 P _8462) = (term956 A P _8462 _8463).
Proof. exact (MK_COMB (@lem400603 A P _8463) (@lem400595 A P _8462 _8463)). Qed.
Lemma lem400615 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term947 A _8463 P _8462) = (term956 A P _8462 _8463).
Proof. exact (TRANS (@lem400580 A _8463 P _8462) (@lem400604 A P _8462 _8463)). Qed.
Lemma lem400616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem400617 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term957 A _8463 P _8462) = (term958 A P _8462 _8463).
Proof. exact (MK_COMB (@lem400616) (@lem400615 A P _8462 _8463)). Qed.
Lemma lem400631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400632 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term953 A _8463 P _8462) = (term954 A P _8462 _8463).
Proof. exact (@lem400631 (term554 A P _8462) (term952 A _8462 _8463)). Qed.
Lemma lem400640 {A : Type'} (P : A -> Prop) (_8463 : A) : (term955 A P _8463) = (term955 A P _8463).
Proof. exact (eq_refl (term955 A P _8463)). Qed.
Lemma lem400641 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : (term951 A _8463 P _8462) = (term956 A P _8462 _8463).
Proof. exact (MK_COMB (@lem400640 A P _8463) (@lem400632 A P _8462 _8463)). Qed.
Lemma lem400652 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : ((term947 A _8463 P _8462) = (term951 A _8463 P _8462)) = ((term956 A P _8462 _8463) = (term956 A P _8462 _8463)).
Proof. exact (MK_COMB (@lem400617 A P _8462 _8463) (@lem400641 A P _8462 _8463)). Qed.
Lemma lem400654 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem400655 (x : Prop) : (x = x) = True.
Proof. exact (@lem400654 Prop x). Qed.
Lemma lem400656 {A : Type'} (P : A -> Prop) (_8462 : A) (_8463 : A) : ((term956 A P _8462 _8463) = (term956 A P _8462 _8463)) = True.
Proof. exact (@lem400655 (term956 A P _8462 _8463)). Qed.
Lemma lem400657 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : ((term947 A _8463 P _8462) = (term951 A _8463 P _8462)) = True.
Proof. exact (TRANS (@lem400652 A P _8462 _8463) (@lem400656 A P _8462 _8463)). Qed.
Lemma lem400658 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : True = ((term947 A _8463 P _8462) = (term951 A _8463 P _8462)).
Proof. exact (SYM (@lem400657 A _8463 P _8462)). Qed.
Lemma lem400659 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term947 A _8463 P _8462) = (term951 A _8463 P _8462).
Proof. exact (EQ_MP (@lem400658 A _8463 P _8462) (@lem0)). Qed.
Lemma lem400660 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : term951 A _8463 P _8462.
Proof. exact (EQ_MP (@lem400659 A _8463 P _8462) (@lem400461 A _8463 P _8462)). Qed.
Lemma lem400662 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem400663 {A : Type'} (_8462 : A) (P : A -> Prop) (_8463 : A) : (term951 A _8463 P _8462) = (term959 A _8462 P _8463).
Proof. exact (@lem400662 (term953 A _8463 P _8462) (P _8463)). Qed.
Lemma lem400665 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem400666 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term960 A _8463 P _8462) = (term961 A _8463 P _8462).
Proof. exact (@lem400665 (term952 A _8462 _8463) (term554 A P _8462)). Qed.
Lemma lem400668 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400669 {A : Type'} (_8462 : A) (_8463 : A) : (term962 A _8462 _8463) = (_8462 = _8463).
Proof. exact (@lem400668 (_8462 = _8463)). Qed.
Lemma lem400670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem400671 {A : Type'} (_8462 : A) (_8463 : A) : (term963 A _8462 _8463) = (term873 A _8462 _8463).
Proof. exact (MK_COMB (@lem400670) (@lem400669 A _8462 _8463)). Qed.
Lemma lem400673 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400674 {A : Type'} (P : A -> Prop) (_8462 : A) : (term964 A P _8462) = (P _8462).
Proof. exact (@lem400673 (P _8462)). Qed.
Lemma lem400675 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term961 A _8463 P _8462) = (term965 A _8463 P _8462).
Proof. exact (MK_COMB (@lem400671 A _8462 _8463) (@lem400674 A P _8462)). Qed.
Lemma lem400676 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term960 A _8463 P _8462) = (term965 A _8463 P _8462).
Proof. exact (TRANS (@lem400666 A _8463 P _8462) (@lem400675 A _8463 P _8462)). Qed.
Lemma lem400677 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem400678 {A : Type'} (_8463 : A) (P : A -> Prop) (_8462 : A) : (term966 A _8463 P _8462) = (term967 A _8463 P _8462).
Proof. exact (MK_COMB (@lem400677) (@lem400676 A _8463 P _8462)). Qed.
Lemma lem400679 {A : Type'} (P : A -> Prop) (_8463 : A) : (P _8463) = (P _8463).
Proof. exact (eq_refl (P _8463)). Qed.
Lemma lem400680 {A : Type'} (_8462 : A) (P : A -> Prop) (_8463 : A) : (term959 A _8462 P _8463) = (term968 A _8462 P _8463).
Proof. exact (MK_COMB (@lem400678 A _8463 P _8462) (@lem400679 A P _8463)). Qed.
Lemma lem400681 {A : Type'} (_8462 : A) (P : A -> Prop) (_8463 : A) : (term951 A _8463 P _8462) = (term968 A _8462 P _8463).
Proof. exact (TRANS (@lem400663 A _8462 P _8463) (@lem400680 A _8462 P _8463)). Qed.
Lemma lem400683 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term969 A P s x.
Proof. exact (conj (@lem400513 A x s h1) (@lem400573 A y P s n x h2 h3)). Qed.
Lemma lem400685 {A : Type'} (_8462 : A) (P : A -> Prop) (_8463 : A) : term968 A _8462 P _8463.
Proof. exact (EQ_MP (@lem400681 A _8462 P _8463) (@lem400660 A _8463 P _8462)). Qed.
Lemma lem400686 {A : Type'} (_8462 : A) (P : A -> Prop) (_8463 : A) : term968 A _8462 P _8463.
Proof. exact (@lem400685 A _8462 P _8463). Qed.
Lemma lem400687 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem400686 A (term597 A s x) P x). Qed.
Lemma lem400690 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (@lem400687 A s P x (@lem400683 A y P s n x h1 h2 h3)). Qed.
Lemma lem400691 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem400690 A y P s n x h1 h2 h3). Qed.
Lemma lem400693 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400694 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem400693 (P x)). Qed.
Lemma lem400695 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (EQ_MP (@lem400694 A P x) (@lem400691 A y P s n x h1 h2 h3)). Qed.
Lemma lem400698 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem400700 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem400698 (P x)). Qed.
Lemma lem400703 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem400700 A P x) (@lem399913 A P x h1)). Qed.
Lemma lem400706 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (@lem400703 A P x h3 (@lem400695 A y P s n x h1 h2 h4)). Qed.
Lemma lem400707 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term180.
Proof. exact (fun h0 : ~ False => @lem400706 A y P s n x h1 h2 h3 h4). Qed.
Lemma lem400709 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400710 : term180 = False.
Proof. exact (@lem400709 False). Qed.
Lemma lem400711 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem400710) (@lem400707 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem400731 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem400732 {A : Type'} (_8478 : A) (_8479 : A) (h1 : _8478 = _8479) : _8478 = _8479.
Proof. exact (h1). Qed.
Lemma lem400733 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) (h1 : _8478 = _8479) : (P _8478) = (P _8479).
Proof. exact (MK_COMB (@lem400731 A P) (@lem400732 A _8478 _8479 h1)). Qed.
Lemma lem400735 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem400736 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : term944 A _8479 P _8478.
Proof. exact (@lem400735 (P _8479) (P _8478)). Qed.
Lemma lem400737 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) (h1 : _8478 = _8479) : term945 A _8479 P _8478.
Proof. exact (@lem400736 A _8479 P _8478 (@lem400733 A P _8478 _8479 h1)). Qed.
Lemma lem400738 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : term946 A _8479 P _8478.
Proof. exact (fun h0 : _8478 = _8479 => @lem400737 A P _8478 _8479 h0). Qed.
Lemma lem400740 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem400741 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term946 A _8479 P _8478) = (term947 A _8479 P _8478).
Proof. exact (@lem400740 (_8478 = _8479) (term945 A _8479 P _8478)). Qed.
Lemma lem400742 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : term947 A _8479 P _8478.
Proof. exact (EQ_MP (@lem400741 A _8479 P _8478) (@lem400738 A _8479 P _8478)). Qed.
Lemma lem400787 {A : Type'} (_8361 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8361) = _8361.
Proof. exact (EQ_MP (@lem399716 A s _8361) (@lem399715 A _8361 s h1)). Qed.
Lemma lem400788 {A : Type'} (_8361 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8361) = _8361.
Proof. exact (@lem400787 A _8361 s h1). Qed.
Lemma lem400789 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem400788 A x s h1). Qed.
Lemma lem400790 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem400789 A x s h1). Qed.
Lemma lem400792 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400793 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem400792 ((term597 A s x) = x)). Qed.
Lemma lem400794 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem400793 A s x) (@lem400790 A x s h1)). Qed.
Lemma lem400796 (_8364 : nat) (h1 : term327) : term325 _8364.
Proof. exact (EQ_MP (@lem399725 _8364) (@lem399724 _8364 h1)). Qed.
Lemma lem400797 (n : nat) (h1 : term327) : term325 n.
Proof. exact (@lem400796 n h1). Qed.
Lemma lem400798 (n : nat) (h1 : term327) : term1186 n.
Proof. exact (fun h0 : term1187 n => @lem400797 n h1). Qed.
Lemma lem400800 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400801 (n : nat) : (term1186 n) = (term325 n).
Proof. exact (@lem400800 (term325 n)). Qed.
Lemma lem400802 (n : nat) (h1 : term327) : term325 n.
Proof. exact (EQ_MP (@lem400801 n) (@lem400798 n h1)). Qed.
Lemma lem400808 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400809 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : (term1174 A n P s x _8365) = (term1188 A P s x _8365 n).
Proof. exact (@lem400808 (term841 A P s x _8365) (term439 _8365 n)). Qed.
Lemma lem400815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem400816 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : (term1189 A n P s x _8365) = (term1190 A P s x _8365 n).
Proof. exact (MK_COMB (@lem400815) (@lem400809 A P s x _8365 n)). Qed.
Lemma lem400822 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : (term1188 A P s x _8365 n) = (term1188 A P s x _8365 n).
Proof. exact (eq_refl (term1188 A P s x _8365 n)). Qed.
Lemma lem400823 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : ((term1174 A n P s x _8365) = (term1188 A P s x _8365 n)) = ((term1188 A P s x _8365 n) = (term1188 A P s x _8365 n)).
Proof. exact (MK_COMB (@lem400816 A P s x _8365 n) (@lem400822 A P s x _8365 n)). Qed.
Lemma lem400825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem400826 (x : Prop) : (x = x) = True.
Proof. exact (@lem400825 Prop x). Qed.
Lemma lem400827 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : ((term1188 A P s x _8365 n) = (term1188 A P s x _8365 n)) = True.
Proof. exact (@lem400826 (term1188 A P s x _8365 n)). Qed.
Lemma lem400828 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : ((term1174 A n P s x _8365) = (term1188 A P s x _8365 n)) = True.
Proof. exact (TRANS (@lem400823 A P s x _8365 n) (@lem400827 A P s x _8365 n)). Qed.
Lemma lem400829 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : True = ((term1174 A n P s x _8365) = (term1188 A P s x _8365 n)).
Proof. exact (SYM (@lem400828 A P s x _8365 n)). Qed.
Lemma lem400830 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) (n : nat) : (term1174 A n P s x _8365) = (term1188 A P s x _8365 n).
Proof. exact (EQ_MP (@lem400829 A P s x _8365 n) (@lem0)). Qed.
Lemma lem400831 {A : Type'} (_8365 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1188 A P s x _8365 n.
Proof. exact (EQ_MP (@lem400830 A P s x _8365 n) (@lem400122 A _8365 y P s n x h1)). Qed.
Lemma lem400833 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem400834 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) : (term1188 A P s x _8365 n) = (term1191 A n P s x _8365).
Proof. exact (@lem400833 (term439 _8365 n) (term841 A P s x _8365)). Qed.
Lemma lem400836 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400837 (_8365 : nat) (n : nat) : (term483 _8365 n) = (term363 _8365 n).
Proof. exact (@lem400836 (term363 _8365 n)). Qed.
Lemma lem400838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem400839 (_8365 : nat) (n : nat) : (term484 _8365 n) = (term485 _8365 n).
Proof. exact (MK_COMB (@lem400838) (@lem400837 _8365 n)). Qed.
Lemma lem400840 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) : (term841 A P s x _8365) = (term841 A P s x _8365).
Proof. exact (eq_refl (term841 A P s x _8365)). Qed.
Lemma lem400841 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) : (term1191 A n P s x _8365) = (term843 A n P s x _8365).
Proof. exact (MK_COMB (@lem400839 _8365 n) (@lem400840 A P s x _8365)). Qed.
Lemma lem400842 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8365 : nat) : (term1188 A P s x _8365 n) = (term843 A n P s x _8365).
Proof. exact (TRANS (@lem400834 A n P s x _8365) (@lem400841 A n P s x _8365)). Qed.
Lemma lem400845 {A : Type'} (_8365 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term843 A n P s x _8365.
Proof. exact (EQ_MP (@lem400842 A n P s x _8365) (@lem400831 A _8365 y P s n x h1)). Qed.
Lemma lem400846 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1192 A n P s x.
Proof. exact (@lem400845 A (NUMERAL 0) y P s n x h1). Qed.
Lemma lem400849 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (@lem400846 A y P s n x h2 (@lem400802 n h1)). Qed.
Lemma lem400850 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem400849 A y P s n x h1 h2). Qed.
Lemma lem400852 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400853 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem400852 (term784 A P s x)). Qed.
Lemma lem400854 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (EQ_MP (@lem400853 A P s x) (@lem400850 A y P s n x h1 h2)). Qed.
Lemma lem400860 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem400861 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term947 A _8479 P _8478) = (term951 A _8479 P _8478).
Proof. exact (@lem400860 (P _8479) (term952 A _8478 _8479) (term554 A P _8478)). Qed.
Lemma lem400875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400876 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term953 A _8479 P _8478) = (term954 A P _8478 _8479).
Proof. exact (@lem400875 (term554 A P _8478) (term952 A _8478 _8479)). Qed.
Lemma lem400884 {A : Type'} (P : A -> Prop) (_8479 : A) : (term955 A P _8479) = (term955 A P _8479).
Proof. exact (eq_refl (term955 A P _8479)). Qed.
Lemma lem400885 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term951 A _8479 P _8478) = (term956 A P _8478 _8479).
Proof. exact (MK_COMB (@lem400884 A P _8479) (@lem400876 A P _8478 _8479)). Qed.
Lemma lem400896 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term947 A _8479 P _8478) = (term956 A P _8478 _8479).
Proof. exact (TRANS (@lem400861 A _8479 P _8478) (@lem400885 A P _8478 _8479)). Qed.
Lemma lem400897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem400898 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term957 A _8479 P _8478) = (term958 A P _8478 _8479).
Proof. exact (MK_COMB (@lem400897) (@lem400896 A P _8478 _8479)). Qed.
Lemma lem400912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem400913 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term953 A _8479 P _8478) = (term954 A P _8478 _8479).
Proof. exact (@lem400912 (term554 A P _8478) (term952 A _8478 _8479)). Qed.
Lemma lem400921 {A : Type'} (P : A -> Prop) (_8479 : A) : (term955 A P _8479) = (term955 A P _8479).
Proof. exact (eq_refl (term955 A P _8479)). Qed.
Lemma lem400922 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : (term951 A _8479 P _8478) = (term956 A P _8478 _8479).
Proof. exact (MK_COMB (@lem400921 A P _8479) (@lem400913 A P _8478 _8479)). Qed.
Lemma lem400933 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : ((term947 A _8479 P _8478) = (term951 A _8479 P _8478)) = ((term956 A P _8478 _8479) = (term956 A P _8478 _8479)).
Proof. exact (MK_COMB (@lem400898 A P _8478 _8479) (@lem400922 A P _8478 _8479)). Qed.
Lemma lem400935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem400936 (x : Prop) : (x = x) = True.
Proof. exact (@lem400935 Prop x). Qed.
Lemma lem400937 {A : Type'} (P : A -> Prop) (_8478 : A) (_8479 : A) : ((term956 A P _8478 _8479) = (term956 A P _8478 _8479)) = True.
Proof. exact (@lem400936 (term956 A P _8478 _8479)). Qed.
Lemma lem400938 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : ((term947 A _8479 P _8478) = (term951 A _8479 P _8478)) = True.
Proof. exact (TRANS (@lem400933 A P _8478 _8479) (@lem400937 A P _8478 _8479)). Qed.
Lemma lem400939 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : True = ((term947 A _8479 P _8478) = (term951 A _8479 P _8478)).
Proof. exact (SYM (@lem400938 A _8479 P _8478)). Qed.
Lemma lem400940 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term947 A _8479 P _8478) = (term951 A _8479 P _8478).
Proof. exact (EQ_MP (@lem400939 A _8479 P _8478) (@lem0)). Qed.
Lemma lem400941 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : term951 A _8479 P _8478.
Proof. exact (EQ_MP (@lem400940 A _8479 P _8478) (@lem400742 A _8479 P _8478)). Qed.
Lemma lem400943 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem400944 {A : Type'} (_8478 : A) (P : A -> Prop) (_8479 : A) : (term951 A _8479 P _8478) = (term959 A _8478 P _8479).
Proof. exact (@lem400943 (term953 A _8479 P _8478) (P _8479)). Qed.
Lemma lem400946 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem400947 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term960 A _8479 P _8478) = (term961 A _8479 P _8478).
Proof. exact (@lem400946 (term952 A _8478 _8479) (term554 A P _8478)). Qed.
Lemma lem400949 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400950 {A : Type'} (_8478 : A) (_8479 : A) : (term962 A _8478 _8479) = (_8478 = _8479).
Proof. exact (@lem400949 (_8478 = _8479)). Qed.
Lemma lem400951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem400952 {A : Type'} (_8478 : A) (_8479 : A) : (term963 A _8478 _8479) = (term873 A _8478 _8479).
Proof. exact (MK_COMB (@lem400951) (@lem400950 A _8478 _8479)). Qed.
Lemma lem400954 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem400955 {A : Type'} (P : A -> Prop) (_8478 : A) : (term964 A P _8478) = (P _8478).
Proof. exact (@lem400954 (P _8478)). Qed.
Lemma lem400956 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term961 A _8479 P _8478) = (term965 A _8479 P _8478).
Proof. exact (MK_COMB (@lem400952 A _8478 _8479) (@lem400955 A P _8478)). Qed.
Lemma lem400957 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term960 A _8479 P _8478) = (term965 A _8479 P _8478).
Proof. exact (TRANS (@lem400947 A _8479 P _8478) (@lem400956 A _8479 P _8478)). Qed.
Lemma lem400958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem400959 {A : Type'} (_8479 : A) (P : A -> Prop) (_8478 : A) : (term966 A _8479 P _8478) = (term967 A _8479 P _8478).
Proof. exact (MK_COMB (@lem400958) (@lem400957 A _8479 P _8478)). Qed.
Lemma lem400960 {A : Type'} (P : A -> Prop) (_8479 : A) : (P _8479) = (P _8479).
Proof. exact (eq_refl (P _8479)). Qed.
Lemma lem400961 {A : Type'} (_8478 : A) (P : A -> Prop) (_8479 : A) : (term959 A _8478 P _8479) = (term968 A _8478 P _8479).
Proof. exact (MK_COMB (@lem400959 A _8479 P _8478) (@lem400960 A P _8479)). Qed.
Lemma lem400962 {A : Type'} (_8478 : A) (P : A -> Prop) (_8479 : A) : (term951 A _8479 P _8478) = (term968 A _8478 P _8479).
Proof. exact (TRANS (@lem400944 A _8478 P _8479) (@lem400961 A _8478 P _8479)). Qed.
Lemma lem400964 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term969 A P s x.
Proof. exact (conj (@lem400794 A x s h1) (@lem400854 A y P s n x h2 h3)). Qed.
Lemma lem400966 {A : Type'} (_8478 : A) (P : A -> Prop) (_8479 : A) : term968 A _8478 P _8479.
Proof. exact (EQ_MP (@lem400962 A _8478 P _8479) (@lem400941 A _8479 P _8478)). Qed.
Lemma lem400967 {A : Type'} (_8478 : A) (P : A -> Prop) (_8479 : A) : term968 A _8478 P _8479.
Proof. exact (@lem400966 A _8478 P _8479). Qed.
Lemma lem400968 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem400967 A (term597 A s x) P x). Qed.
Lemma lem400971 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (@lem400968 A s P x (@lem400964 A y P s n x h1 h2 h3)). Qed.
Lemma lem400972 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem400971 A y P s n x h1 h2 h3). Qed.
Lemma lem400974 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400975 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem400974 (P x)). Qed.
Lemma lem400976 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (EQ_MP (@lem400975 A P x) (@lem400972 A y P s n x h1 h2 h3)). Qed.
Lemma lem400979 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem400981 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem400979 (P x)). Qed.
Lemma lem400984 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem400981 A P x) (@lem400052 A P x h1)). Qed.
Lemma lem400987 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (@lem400984 A P x h3 (@lem400976 A y P s n x h1 h2 h4)). Qed.
Lemma lem400988 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term180.
Proof. exact (fun h0 : ~ False => @lem400987 A y P s n x h1 h2 h3 h4). Qed.
Lemma lem400990 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem400991 : term180 = False.
Proof. exact (@lem400990 False). Qed.
Lemma lem400992 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem400991) (@lem400988 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem401012 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem401013 {A : Type'} (_8494 : A) (_8495 : A) (h1 : _8494 = _8495) : _8494 = _8495.
Proof. exact (h1). Qed.
Lemma lem401014 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) (h1 : _8494 = _8495) : (P _8494) = (P _8495).
Proof. exact (MK_COMB (@lem401012 A P) (@lem401013 A _8494 _8495 h1)). Qed.
Lemma lem401016 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem401017 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : term944 A _8495 P _8494.
Proof. exact (@lem401016 (P _8495) (P _8494)). Qed.
Lemma lem401018 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) (h1 : _8494 = _8495) : term945 A _8495 P _8494.
Proof. exact (@lem401017 A _8495 P _8494 (@lem401014 A P _8494 _8495 h1)). Qed.
Lemma lem401019 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : term946 A _8495 P _8494.
Proof. exact (fun h0 : _8494 = _8495 => @lem401018 A P _8494 _8495 h0). Qed.
Lemma lem401021 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem401022 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term946 A _8495 P _8494) = (term947 A _8495 P _8494).
Proof. exact (@lem401021 (_8494 = _8495) (term945 A _8495 P _8494)). Qed.
Lemma lem401023 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : term947 A _8495 P _8494.
Proof. exact (EQ_MP (@lem401022 A _8495 P _8494) (@lem401019 A _8495 P _8494)). Qed.
Lemma lem401068 {A : Type'} (_8366 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8366) = _8366.
Proof. exact (EQ_MP (@lem399731 A s _8366) (@lem399730 A _8366 s h1)). Qed.
Lemma lem401069 {A : Type'} (_8366 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8366) = _8366.
Proof. exact (@lem401068 A _8366 s h1). Qed.
Lemma lem401070 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem401069 A x s h1). Qed.
Lemma lem401071 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem401070 A x s h1). Qed.
Lemma lem401073 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401074 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem401073 ((term597 A s x) = x)). Qed.
Lemma lem401075 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem401074 A s x) (@lem401071 A x s h1)). Qed.
Lemma lem401077 (_8369 : nat) (h1 : term327) : term325 _8369.
Proof. exact (EQ_MP (@lem399740 _8369) (@lem399739 _8369 h1)). Qed.
Lemma lem401078 (n : nat) (h1 : term327) : term325 n.
Proof. exact (@lem401077 n h1). Qed.
Lemma lem401079 (n : nat) (h1 : term327) : term1186 n.
Proof. exact (fun h0 : term1187 n => @lem401078 n h1). Qed.
Lemma lem401081 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401082 (n : nat) : (term1186 n) = (term325 n).
Proof. exact (@lem401081 (term325 n)). Qed.
Lemma lem401083 (n : nat) (h1 : term327) : term325 n.
Proof. exact (EQ_MP (@lem401082 n) (@lem401079 n h1)). Qed.
Lemma lem401089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401090 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : (term1174 A n P s x _8370) = (term1188 A P s x _8370 n).
Proof. exact (@lem401089 (term841 A P s x _8370) (term439 _8370 n)). Qed.
Lemma lem401096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem401097 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : (term1189 A n P s x _8370) = (term1190 A P s x _8370 n).
Proof. exact (MK_COMB (@lem401096) (@lem401090 A P s x _8370 n)). Qed.
Lemma lem401103 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : (term1188 A P s x _8370 n) = (term1188 A P s x _8370 n).
Proof. exact (eq_refl (term1188 A P s x _8370 n)). Qed.
Lemma lem401104 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : ((term1174 A n P s x _8370) = (term1188 A P s x _8370 n)) = ((term1188 A P s x _8370 n) = (term1188 A P s x _8370 n)).
Proof. exact (MK_COMB (@lem401097 A P s x _8370 n) (@lem401103 A P s x _8370 n)). Qed.
Lemma lem401106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem401107 (x : Prop) : (x = x) = True.
Proof. exact (@lem401106 Prop x). Qed.
Lemma lem401108 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : ((term1188 A P s x _8370 n) = (term1188 A P s x _8370 n)) = True.
Proof. exact (@lem401107 (term1188 A P s x _8370 n)). Qed.
Lemma lem401109 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : ((term1174 A n P s x _8370) = (term1188 A P s x _8370 n)) = True.
Proof. exact (TRANS (@lem401104 A P s x _8370 n) (@lem401108 A P s x _8370 n)). Qed.
Lemma lem401110 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : True = ((term1174 A n P s x _8370) = (term1188 A P s x _8370 n)).
Proof. exact (SYM (@lem401109 A P s x _8370 n)). Qed.
Lemma lem401111 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) (n : nat) : (term1174 A n P s x _8370) = (term1188 A P s x _8370 n).
Proof. exact (EQ_MP (@lem401110 A P s x _8370 n) (@lem0)). Qed.
Lemma lem401112 {A : Type'} (_8370 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1188 A P s x _8370 n.
Proof. exact (EQ_MP (@lem401111 A P s x _8370 n) (@lem400262 A _8370 y P s n x h1)). Qed.
Lemma lem401114 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem401115 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) : (term1188 A P s x _8370 n) = (term1191 A n P s x _8370).
Proof. exact (@lem401114 (term439 _8370 n) (term841 A P s x _8370)). Qed.
Lemma lem401117 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401118 (_8370 : nat) (n : nat) : (term483 _8370 n) = (term363 _8370 n).
Proof. exact (@lem401117 (term363 _8370 n)). Qed.
Lemma lem401119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401120 (_8370 : nat) (n : nat) : (term484 _8370 n) = (term485 _8370 n).
Proof. exact (MK_COMB (@lem401119) (@lem401118 _8370 n)). Qed.
Lemma lem401121 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) : (term841 A P s x _8370) = (term841 A P s x _8370).
Proof. exact (eq_refl (term841 A P s x _8370)). Qed.
Lemma lem401122 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) : (term1191 A n P s x _8370) = (term843 A n P s x _8370).
Proof. exact (MK_COMB (@lem401120 _8370 n) (@lem401121 A P s x _8370)). Qed.
Lemma lem401123 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8370 : nat) : (term1188 A P s x _8370 n) = (term843 A n P s x _8370).
Proof. exact (TRANS (@lem401115 A n P s x _8370) (@lem401122 A n P s x _8370)). Qed.
Lemma lem401126 {A : Type'} (_8370 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term843 A n P s x _8370.
Proof. exact (EQ_MP (@lem401123 A n P s x _8370) (@lem401112 A _8370 y P s n x h1)). Qed.
Lemma lem401127 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1192 A n P s x.
Proof. exact (@lem401126 A (NUMERAL 0) y P s n x h1). Qed.
Lemma lem401130 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (@lem401127 A y P s n x h2 (@lem401083 n h1)). Qed.
Lemma lem401131 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem401130 A y P s n x h1 h2). Qed.
Lemma lem401133 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401134 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem401133 (term784 A P s x)). Qed.
Lemma lem401135 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (EQ_MP (@lem401134 A P s x) (@lem401131 A y P s n x h1 h2)). Qed.
Lemma lem401141 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem401142 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term947 A _8495 P _8494) = (term951 A _8495 P _8494).
Proof. exact (@lem401141 (P _8495) (term952 A _8494 _8495) (term554 A P _8494)). Qed.
Lemma lem401156 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401157 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term953 A _8495 P _8494) = (term954 A P _8494 _8495).
Proof. exact (@lem401156 (term554 A P _8494) (term952 A _8494 _8495)). Qed.
Lemma lem401165 {A : Type'} (P : A -> Prop) (_8495 : A) : (term955 A P _8495) = (term955 A P _8495).
Proof. exact (eq_refl (term955 A P _8495)). Qed.
Lemma lem401166 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term951 A _8495 P _8494) = (term956 A P _8494 _8495).
Proof. exact (MK_COMB (@lem401165 A P _8495) (@lem401157 A P _8494 _8495)). Qed.
Lemma lem401177 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term947 A _8495 P _8494) = (term956 A P _8494 _8495).
Proof. exact (TRANS (@lem401142 A _8495 P _8494) (@lem401166 A P _8494 _8495)). Qed.
Lemma lem401178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem401179 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term957 A _8495 P _8494) = (term958 A P _8494 _8495).
Proof. exact (MK_COMB (@lem401178) (@lem401177 A P _8494 _8495)). Qed.
Lemma lem401193 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401194 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term953 A _8495 P _8494) = (term954 A P _8494 _8495).
Proof. exact (@lem401193 (term554 A P _8494) (term952 A _8494 _8495)). Qed.
Lemma lem401202 {A : Type'} (P : A -> Prop) (_8495 : A) : (term955 A P _8495) = (term955 A P _8495).
Proof. exact (eq_refl (term955 A P _8495)). Qed.
Lemma lem401203 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : (term951 A _8495 P _8494) = (term956 A P _8494 _8495).
Proof. exact (MK_COMB (@lem401202 A P _8495) (@lem401194 A P _8494 _8495)). Qed.
Lemma lem401214 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : ((term947 A _8495 P _8494) = (term951 A _8495 P _8494)) = ((term956 A P _8494 _8495) = (term956 A P _8494 _8495)).
Proof. exact (MK_COMB (@lem401179 A P _8494 _8495) (@lem401203 A P _8494 _8495)). Qed.
Lemma lem401216 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem401217 (x : Prop) : (x = x) = True.
Proof. exact (@lem401216 Prop x). Qed.
Lemma lem401218 {A : Type'} (P : A -> Prop) (_8494 : A) (_8495 : A) : ((term956 A P _8494 _8495) = (term956 A P _8494 _8495)) = True.
Proof. exact (@lem401217 (term956 A P _8494 _8495)). Qed.
Lemma lem401219 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : ((term947 A _8495 P _8494) = (term951 A _8495 P _8494)) = True.
Proof. exact (TRANS (@lem401214 A P _8494 _8495) (@lem401218 A P _8494 _8495)). Qed.
Lemma lem401220 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : True = ((term947 A _8495 P _8494) = (term951 A _8495 P _8494)).
Proof. exact (SYM (@lem401219 A _8495 P _8494)). Qed.
Lemma lem401221 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term947 A _8495 P _8494) = (term951 A _8495 P _8494).
Proof. exact (EQ_MP (@lem401220 A _8495 P _8494) (@lem0)). Qed.
Lemma lem401222 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : term951 A _8495 P _8494.
Proof. exact (EQ_MP (@lem401221 A _8495 P _8494) (@lem401023 A _8495 P _8494)). Qed.
Lemma lem401224 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem401225 {A : Type'} (_8494 : A) (P : A -> Prop) (_8495 : A) : (term951 A _8495 P _8494) = (term959 A _8494 P _8495).
Proof. exact (@lem401224 (term953 A _8495 P _8494) (P _8495)). Qed.
Lemma lem401227 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem401228 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term960 A _8495 P _8494) = (term961 A _8495 P _8494).
Proof. exact (@lem401227 (term952 A _8494 _8495) (term554 A P _8494)). Qed.
Lemma lem401230 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401231 {A : Type'} (_8494 : A) (_8495 : A) : (term962 A _8494 _8495) = (_8494 = _8495).
Proof. exact (@lem401230 (_8494 = _8495)). Qed.
Lemma lem401232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem401233 {A : Type'} (_8494 : A) (_8495 : A) : (term963 A _8494 _8495) = (term873 A _8494 _8495).
Proof. exact (MK_COMB (@lem401232) (@lem401231 A _8494 _8495)). Qed.
Lemma lem401235 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401236 {A : Type'} (P : A -> Prop) (_8494 : A) : (term964 A P _8494) = (P _8494).
Proof. exact (@lem401235 (P _8494)). Qed.
Lemma lem401237 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term961 A _8495 P _8494) = (term965 A _8495 P _8494).
Proof. exact (MK_COMB (@lem401233 A _8494 _8495) (@lem401236 A P _8494)). Qed.
Lemma lem401238 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term960 A _8495 P _8494) = (term965 A _8495 P _8494).
Proof. exact (TRANS (@lem401228 A _8495 P _8494) (@lem401237 A _8495 P _8494)). Qed.
Lemma lem401239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401240 {A : Type'} (_8495 : A) (P : A -> Prop) (_8494 : A) : (term966 A _8495 P _8494) = (term967 A _8495 P _8494).
Proof. exact (MK_COMB (@lem401239) (@lem401238 A _8495 P _8494)). Qed.
Lemma lem401241 {A : Type'} (P : A -> Prop) (_8495 : A) : (P _8495) = (P _8495).
Proof. exact (eq_refl (P _8495)). Qed.
Lemma lem401242 {A : Type'} (_8494 : A) (P : A -> Prop) (_8495 : A) : (term959 A _8494 P _8495) = (term968 A _8494 P _8495).
Proof. exact (MK_COMB (@lem401240 A _8495 P _8494) (@lem401241 A P _8495)). Qed.
Lemma lem401243 {A : Type'} (_8494 : A) (P : A -> Prop) (_8495 : A) : (term951 A _8495 P _8494) = (term968 A _8494 P _8495).
Proof. exact (TRANS (@lem401225 A _8494 P _8495) (@lem401242 A _8494 P _8495)). Qed.
Lemma lem401245 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term969 A P s x.
Proof. exact (conj (@lem401075 A x s h1) (@lem401135 A y P s n x h2 h3)). Qed.
Lemma lem401247 {A : Type'} (_8494 : A) (P : A -> Prop) (_8495 : A) : term968 A _8494 P _8495.
Proof. exact (EQ_MP (@lem401243 A _8494 P _8495) (@lem401222 A _8495 P _8494)). Qed.
Lemma lem401248 {A : Type'} (_8494 : A) (P : A -> Prop) (_8495 : A) : term968 A _8494 P _8495.
Proof. exact (@lem401247 A _8494 P _8495). Qed.
Lemma lem401249 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem401248 A (term597 A s x) P x). Qed.
Lemma lem401252 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (@lem401249 A s P x (@lem401245 A y P s n x h1 h2 h3)). Qed.
Lemma lem401253 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem401252 A y P s n x h1 h2 h3). Qed.
Lemma lem401255 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401256 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem401255 (P x)). Qed.
Lemma lem401257 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (EQ_MP (@lem401256 A P x) (@lem401253 A y P s n x h1 h2 h3)). Qed.
Lemma lem401260 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem401262 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem401260 (P x)). Qed.
Lemma lem401265 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem401262 A P x) (@lem400192 A P x h1)). Qed.
Lemma lem401268 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (@lem401265 A P x h3 (@lem401257 A y P s n x h1 h2 h4)). Qed.
Lemma lem401269 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term180.
Proof. exact (fun h0 : ~ False => @lem401268 A y P s n x h1 h2 h3 h4). Qed.
Lemma lem401271 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401272 : term180 = False.
Proof. exact (@lem401271 False). Qed.
Lemma lem401273 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401272) (@lem401269 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem401293 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem401294 {A : Type'} (_8510 : A) (_8511 : A) (h1 : _8510 = _8511) : _8510 = _8511.
Proof. exact (h1). Qed.
Lemma lem401295 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) (h1 : _8510 = _8511) : (P _8510) = (P _8511).
Proof. exact (MK_COMB (@lem401293 A P) (@lem401294 A _8510 _8511 h1)). Qed.
Lemma lem401297 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem401298 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : term944 A _8511 P _8510.
Proof. exact (@lem401297 (P _8511) (P _8510)). Qed.
Lemma lem401299 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) (h1 : _8510 = _8511) : term945 A _8511 P _8510.
Proof. exact (@lem401298 A _8511 P _8510 (@lem401295 A P _8510 _8511 h1)). Qed.
Lemma lem401300 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : term946 A _8511 P _8510.
Proof. exact (fun h0 : _8510 = _8511 => @lem401299 A P _8510 _8511 h0). Qed.
Lemma lem401302 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem401303 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term946 A _8511 P _8510) = (term947 A _8511 P _8510).
Proof. exact (@lem401302 (_8510 = _8511) (term945 A _8511 P _8510)). Qed.
Lemma lem401304 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : term947 A _8511 P _8510.
Proof. exact (EQ_MP (@lem401303 A _8511 P _8510) (@lem401300 A _8511 P _8510)). Qed.
Lemma lem401349 {A : Type'} (_8371 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8371) = _8371.
Proof. exact (EQ_MP (@lem399746 A s _8371) (@lem399745 A _8371 s h1)). Qed.
Lemma lem401350 {A : Type'} (_8371 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8371) = _8371.
Proof. exact (@lem401349 A _8371 s h1). Qed.
Lemma lem401351 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem401350 A x s h1). Qed.
Lemma lem401352 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem401351 A x s h1). Qed.
Lemma lem401354 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401355 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem401354 ((term597 A s x) = x)). Qed.
Lemma lem401356 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem401355 A s x) (@lem401352 A x s h1)). Qed.
Lemma lem401358 (_8374 : nat) (h1 : term327) : term325 _8374.
Proof. exact (EQ_MP (@lem399755 _8374) (@lem399754 _8374 h1)). Qed.
Lemma lem401359 (n : nat) (h1 : term327) : term325 n.
Proof. exact (@lem401358 n h1). Qed.
Lemma lem401360 (n : nat) (h1 : term327) : term1186 n.
Proof. exact (fun h0 : term1187 n => @lem401359 n h1). Qed.
Lemma lem401362 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401363 (n : nat) : (term1186 n) = (term325 n).
Proof. exact (@lem401362 (term325 n)). Qed.
Lemma lem401364 (n : nat) (h1 : term327) : term325 n.
Proof. exact (EQ_MP (@lem401363 n) (@lem401360 n h1)). Qed.
Lemma lem401370 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401371 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : (term1174 A n P s x _8375) = (term1188 A P s x _8375 n).
Proof. exact (@lem401370 (term841 A P s x _8375) (term439 _8375 n)). Qed.
Lemma lem401377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem401378 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : (term1189 A n P s x _8375) = (term1190 A P s x _8375 n).
Proof. exact (MK_COMB (@lem401377) (@lem401371 A P s x _8375 n)). Qed.
Lemma lem401384 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : (term1188 A P s x _8375 n) = (term1188 A P s x _8375 n).
Proof. exact (eq_refl (term1188 A P s x _8375 n)). Qed.
Lemma lem401385 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : ((term1174 A n P s x _8375) = (term1188 A P s x _8375 n)) = ((term1188 A P s x _8375 n) = (term1188 A P s x _8375 n)).
Proof. exact (MK_COMB (@lem401378 A P s x _8375 n) (@lem401384 A P s x _8375 n)). Qed.
Lemma lem401387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem401388 (x : Prop) : (x = x) = True.
Proof. exact (@lem401387 Prop x). Qed.
Lemma lem401389 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : ((term1188 A P s x _8375 n) = (term1188 A P s x _8375 n)) = True.
Proof. exact (@lem401388 (term1188 A P s x _8375 n)). Qed.
Lemma lem401390 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : ((term1174 A n P s x _8375) = (term1188 A P s x _8375 n)) = True.
Proof. exact (TRANS (@lem401385 A P s x _8375 n) (@lem401389 A P s x _8375 n)). Qed.
Lemma lem401391 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : True = ((term1174 A n P s x _8375) = (term1188 A P s x _8375 n)).
Proof. exact (SYM (@lem401390 A P s x _8375 n)). Qed.
Lemma lem401392 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) (n : nat) : (term1174 A n P s x _8375) = (term1188 A P s x _8375 n).
Proof. exact (EQ_MP (@lem401391 A P s x _8375 n) (@lem0)). Qed.
Lemma lem401393 {A : Type'} (_8375 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1188 A P s x _8375 n.
Proof. exact (EQ_MP (@lem401392 A P s x _8375 n) (@lem400416 A _8375 y P s n x h1)). Qed.
Lemma lem401395 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem401396 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) : (term1188 A P s x _8375 n) = (term1191 A n P s x _8375).
Proof. exact (@lem401395 (term439 _8375 n) (term841 A P s x _8375)). Qed.
Lemma lem401398 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401399 (_8375 : nat) (n : nat) : (term483 _8375 n) = (term363 _8375 n).
Proof. exact (@lem401398 (term363 _8375 n)). Qed.
Lemma lem401400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401401 (_8375 : nat) (n : nat) : (term484 _8375 n) = (term485 _8375 n).
Proof. exact (MK_COMB (@lem401400) (@lem401399 _8375 n)). Qed.
Lemma lem401402 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) : (term841 A P s x _8375) = (term841 A P s x _8375).
Proof. exact (eq_refl (term841 A P s x _8375)). Qed.
Lemma lem401403 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) : (term1191 A n P s x _8375) = (term843 A n P s x _8375).
Proof. exact (MK_COMB (@lem401401 _8375 n) (@lem401402 A P s x _8375)). Qed.
Lemma lem401404 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8375 : nat) : (term1188 A P s x _8375 n) = (term843 A n P s x _8375).
Proof. exact (TRANS (@lem401396 A n P s x _8375) (@lem401403 A n P s x _8375)). Qed.
Lemma lem401407 {A : Type'} (_8375 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term843 A n P s x _8375.
Proof. exact (EQ_MP (@lem401404 A n P s x _8375) (@lem401393 A _8375 y P s n x h1)). Qed.
Lemma lem401408 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term1053 A y P s n x) : term1192 A n P s x.
Proof. exact (@lem401407 A (NUMERAL 0) y P s n x h1). Qed.
Lemma lem401411 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (@lem401408 A y P s n x h2 (@lem401364 n h1)). Qed.
Lemma lem401412 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem401411 A y P s n x h1 h2). Qed.
Lemma lem401414 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401415 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem401414 (term784 A P s x)). Qed.
Lemma lem401416 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term327) (h2 : term1053 A y P s n x) : term784 A P s x.
Proof. exact (EQ_MP (@lem401415 A P s x) (@lem401412 A y P s n x h1 h2)). Qed.
Lemma lem401422 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem401423 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term947 A _8511 P _8510) = (term951 A _8511 P _8510).
Proof. exact (@lem401422 (P _8511) (term952 A _8510 _8511) (term554 A P _8510)). Qed.
Lemma lem401437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401438 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term953 A _8511 P _8510) = (term954 A P _8510 _8511).
Proof. exact (@lem401437 (term554 A P _8510) (term952 A _8510 _8511)). Qed.
Lemma lem401446 {A : Type'} (P : A -> Prop) (_8511 : A) : (term955 A P _8511) = (term955 A P _8511).
Proof. exact (eq_refl (term955 A P _8511)). Qed.
Lemma lem401447 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term951 A _8511 P _8510) = (term956 A P _8510 _8511).
Proof. exact (MK_COMB (@lem401446 A P _8511) (@lem401438 A P _8510 _8511)). Qed.
Lemma lem401458 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term947 A _8511 P _8510) = (term956 A P _8510 _8511).
Proof. exact (TRANS (@lem401423 A _8511 P _8510) (@lem401447 A P _8510 _8511)). Qed.
Lemma lem401459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem401460 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term957 A _8511 P _8510) = (term958 A P _8510 _8511).
Proof. exact (MK_COMB (@lem401459) (@lem401458 A P _8510 _8511)). Qed.
Lemma lem401474 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem401475 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term953 A _8511 P _8510) = (term954 A P _8510 _8511).
Proof. exact (@lem401474 (term554 A P _8510) (term952 A _8510 _8511)). Qed.
Lemma lem401483 {A : Type'} (P : A -> Prop) (_8511 : A) : (term955 A P _8511) = (term955 A P _8511).
Proof. exact (eq_refl (term955 A P _8511)). Qed.
Lemma lem401484 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : (term951 A _8511 P _8510) = (term956 A P _8510 _8511).
Proof. exact (MK_COMB (@lem401483 A P _8511) (@lem401475 A P _8510 _8511)). Qed.
Lemma lem401495 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : ((term947 A _8511 P _8510) = (term951 A _8511 P _8510)) = ((term956 A P _8510 _8511) = (term956 A P _8510 _8511)).
Proof. exact (MK_COMB (@lem401460 A P _8510 _8511) (@lem401484 A P _8510 _8511)). Qed.
Lemma lem401497 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem401498 (x : Prop) : (x = x) = True.
Proof. exact (@lem401497 Prop x). Qed.
Lemma lem401499 {A : Type'} (P : A -> Prop) (_8510 : A) (_8511 : A) : ((term956 A P _8510 _8511) = (term956 A P _8510 _8511)) = True.
Proof. exact (@lem401498 (term956 A P _8510 _8511)). Qed.
Lemma lem401500 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : ((term947 A _8511 P _8510) = (term951 A _8511 P _8510)) = True.
Proof. exact (TRANS (@lem401495 A P _8510 _8511) (@lem401499 A P _8510 _8511)). Qed.
Lemma lem401501 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : True = ((term947 A _8511 P _8510) = (term951 A _8511 P _8510)).
Proof. exact (SYM (@lem401500 A _8511 P _8510)). Qed.
Lemma lem401502 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term947 A _8511 P _8510) = (term951 A _8511 P _8510).
Proof. exact (EQ_MP (@lem401501 A _8511 P _8510) (@lem0)). Qed.
Lemma lem401503 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : term951 A _8511 P _8510.
Proof. exact (EQ_MP (@lem401502 A _8511 P _8510) (@lem401304 A _8511 P _8510)). Qed.
Lemma lem401505 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem401506 {A : Type'} (_8510 : A) (P : A -> Prop) (_8511 : A) : (term951 A _8511 P _8510) = (term959 A _8510 P _8511).
Proof. exact (@lem401505 (term953 A _8511 P _8510) (P _8511)). Qed.
Lemma lem401508 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem401509 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term960 A _8511 P _8510) = (term961 A _8511 P _8510).
Proof. exact (@lem401508 (term952 A _8510 _8511) (term554 A P _8510)). Qed.
Lemma lem401511 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401512 {A : Type'} (_8510 : A) (_8511 : A) : (term962 A _8510 _8511) = (_8510 = _8511).
Proof. exact (@lem401511 (_8510 = _8511)). Qed.
Lemma lem401513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem401514 {A : Type'} (_8510 : A) (_8511 : A) : (term963 A _8510 _8511) = (term873 A _8510 _8511).
Proof. exact (MK_COMB (@lem401513) (@lem401512 A _8510 _8511)). Qed.
Lemma lem401516 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem401517 {A : Type'} (P : A -> Prop) (_8510 : A) : (term964 A P _8510) = (P _8510).
Proof. exact (@lem401516 (P _8510)). Qed.
Lemma lem401518 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term961 A _8511 P _8510) = (term965 A _8511 P _8510).
Proof. exact (MK_COMB (@lem401514 A _8510 _8511) (@lem401517 A P _8510)). Qed.
Lemma lem401519 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term960 A _8511 P _8510) = (term965 A _8511 P _8510).
Proof. exact (TRANS (@lem401509 A _8511 P _8510) (@lem401518 A _8511 P _8510)). Qed.
Lemma lem401520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401521 {A : Type'} (_8511 : A) (P : A -> Prop) (_8510 : A) : (term966 A _8511 P _8510) = (term967 A _8511 P _8510).
Proof. exact (MK_COMB (@lem401520) (@lem401519 A _8511 P _8510)). Qed.
Lemma lem401522 {A : Type'} (P : A -> Prop) (_8511 : A) : (P _8511) = (P _8511).
Proof. exact (eq_refl (P _8511)). Qed.
Lemma lem401523 {A : Type'} (_8510 : A) (P : A -> Prop) (_8511 : A) : (term959 A _8510 P _8511) = (term968 A _8510 P _8511).
Proof. exact (MK_COMB (@lem401521 A _8511 P _8510) (@lem401522 A P _8511)). Qed.
Lemma lem401524 {A : Type'} (_8510 : A) (P : A -> Prop) (_8511 : A) : (term951 A _8511 P _8510) = (term968 A _8510 P _8511).
Proof. exact (TRANS (@lem401506 A _8510 P _8511) (@lem401523 A _8510 P _8511)). Qed.
Lemma lem401526 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term969 A P s x.
Proof. exact (conj (@lem401356 A x s h1) (@lem401416 A y P s n x h2 h3)). Qed.
Lemma lem401528 {A : Type'} (_8510 : A) (P : A -> Prop) (_8511 : A) : term968 A _8510 P _8511.
Proof. exact (EQ_MP (@lem401524 A _8510 P _8511) (@lem401503 A _8511 P _8510)). Qed.
Lemma lem401529 {A : Type'} (_8510 : A) (P : A -> Prop) (_8511 : A) : term968 A _8510 P _8511.
Proof. exact (@lem401528 A _8510 P _8511). Qed.
Lemma lem401530 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem401529 A (term597 A s x) P x). Qed.
Lemma lem401533 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (@lem401530 A s P x (@lem401526 A y P s n x h1 h2 h3)). Qed.
Lemma lem401534 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem401533 A y P s n x h1 h2 h3). Qed.
Lemma lem401536 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401537 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem401536 (P x)). Qed.
Lemma lem401538 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term1053 A y P s n x) : P x.
Proof. exact (EQ_MP (@lem401537 A P x) (@lem401534 A y P s n x h1 h2 h3)). Qed.
Lemma lem401541 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem401543 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem401541 (P x)). Qed.
Lemma lem401546 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem401543 A P x) (@lem400346 A P x h1)). Qed.
Lemma lem401549 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (@lem401546 A P x h3 (@lem401538 A y P s n x h1 h2 h4)). Qed.
Lemma lem401550 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term180.
Proof. exact (fun h0 : ~ False => @lem401549 A y P s n x h1 h2 h3 h4). Qed.
Lemma lem401552 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem401553 : term180 = False.
Proof. exact (@lem401552 False). Qed.
Lemma lem401554 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401553) (@lem401550 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem401555 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401554 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem400346 A P x h3)). Qed.
Lemma lem401557 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401555 A y P s n x h1 h2 h3 h4) (@lem400346 A P x h3)). Qed.
Lemma lem401558 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401273 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem400192 A P x h3)). Qed.
Lemma lem401560 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401558 A y P s n x h1 h2 h3 h4) (@lem400192 A P x h3)). Qed.
Lemma lem401561 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem400992 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem400052 A P x h3)). Qed.
Lemma lem401563 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401561 A y P s n x h1 h2 h3 h4) (@lem400052 A P x h3)). Qed.
Lemma lem401564 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem400711 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399913 A P x h3)). Qed.
Lemma lem401566 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401564 A y P s n x h1 h2 h3 h4) (@lem399913 A P x h3)). Qed.
Lemma lem401567 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401557 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399839 A P x h3)). Qed.
Lemma lem401568 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401567 A y P s n x h1 h2 h3 h4) (@lem399839 A P x h3)). Qed.
Lemma lem401569 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401560 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399813 A P x h3)). Qed.
Lemma lem401570 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401569 A y P s n x h1 h2 h3 h4) (@lem399813 A P x h3)). Qed.
Lemma lem401571 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401563 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399789 A P x h3)). Qed.
Lemma lem401572 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401571 A y P s n x h1 h2 h3 h4) (@lem399789 A P x h3)). Qed.
Lemma lem401573 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401566 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399765 A P x h3)). Qed.
Lemma lem401574 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401573 A y P s n x h1 h2 h3 h4) (@lem399765 A P x h3)). Qed.
Lemma lem401575 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401568 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399659 A P x h3)). Qed.
Lemma lem401576 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401575 A y P s n x h1 h2 h3 h4) (@lem399659 A P x h3)). Qed.
Lemma lem401577 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401570 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399594 A P x h3)). Qed.
Lemma lem401578 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401577 A y P s n x h1 h2 h3 h4) (@lem399594 A P x h3)). Qed.
Lemma lem401579 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401572 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399533 A P x h3)). Qed.
Lemma lem401580 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401579 A y P s n x h1 h2 h3 h4) (@lem399533 A P x h3)). Qed.
Lemma lem401581 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401574 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399472 A P x h3)). Qed.
Lemma lem401582 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401581 A y P s n x h1 h2 h3 h4) (@lem399472 A P x h3)). Qed.
Lemma lem401583 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term327 = False.
Proof. exact (prop_ext (fun h5 : term327 => @lem401576 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399666 h2)). Qed.
Lemma lem401584 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401583 A y P s n x h1 h2 h3 h4) (@lem399666 h2)). Qed.
Lemma lem401585 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401584 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399659 A P x h3)). Qed.
Lemma lem401586 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401585 A y P s n x h1 h2 h3 h4) (@lem399659 A P x h3)). Qed.
Lemma lem401587 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem401586 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399645 A s h1)). Qed.
Lemma lem401588 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401587 A y P s n x h1 h2 h3 h4) (@lem399645 A s h1)). Qed.
Lemma lem401589 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term327 = False.
Proof. exact (prop_ext (fun h5 : term327 => @lem401578 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399601 h2)). Qed.
Lemma lem401590 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401589 A y P s n x h1 h2 h3 h4) (@lem399601 h2)). Qed.
Lemma lem401591 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401590 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399594 A P x h3)). Qed.
Lemma lem401592 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401591 A y P s n x h1 h2 h3 h4) (@lem399594 A P x h3)). Qed.
Lemma lem401593 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem401592 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399580 A s h1)). Qed.
Lemma lem401594 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401593 A y P s n x h1 h2 h3 h4) (@lem399580 A s h1)). Qed.
Lemma lem401595 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term327 = False.
Proof. exact (prop_ext (fun h5 : term327 => @lem401580 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399540 h2)). Qed.
Lemma lem401596 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401595 A y P s n x h1 h2 h3 h4) (@lem399540 h2)). Qed.
Lemma lem401597 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401596 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399533 A P x h3)). Qed.
Lemma lem401598 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401597 A y P s n x h1 h2 h3 h4) (@lem399533 A P x h3)). Qed.
Lemma lem401599 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem401598 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399519 A s h1)). Qed.
Lemma lem401600 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401599 A y P s n x h1 h2 h3 h4) (@lem399519 A s h1)). Qed.
Lemma lem401601 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : term327 = False.
Proof. exact (prop_ext (fun h5 : term327 => @lem401582 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399479 h2)). Qed.
Lemma lem401602 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401601 A y P s n x h1 h2 h3 h4) (@lem399479 h2)). Qed.
Lemma lem401603 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem401602 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399472 A P x h3)). Qed.
Lemma lem401604 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401603 A y P s n x h1 h2 h3 h4) (@lem399472 A P x h3)). Qed.
Lemma lem401605 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem401604 A y P s n x h1 h2 h3 h4) (fun h5 : False => @lem399458 A s h1)). Qed.
Lemma lem401606 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401605 A y P s n x h1 h2 h3 h4) (@lem399458 A s h1)). Qed.
Lemma lem401607 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1135 A n P s x m) : False.
Proof. exact (or_elim (@lem399447 A n P s x m h5) (fun h0 : term841 A P s x n => @lem401600 A y P s n x h1 h2 h3 h4) (fun h0 : term1104 A n P s x m => @lem401594 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem401608 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1149 A y n P s x m) : False.
Proof. exact (or_elim (@lem399444 A y n P s x m h5) (fun h0 : term1142 A y s x n => @lem401606 A y P s n x h1 h2 h3 h4) (fun h0 : term1135 A n P s x m => @lem401607 A y n P s x m h1 h2 h3 h4 h0)). Qed.
Lemma lem401609 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : False.
Proof. exact (or_elim (@lem399427 A y P m s n x h5) (fun h0 : term1149 A y n P s x m => @lem401608 A y n P s x m h1 h2 h3 h4 h0) (fun h0 : (s x n) = x => @lem401588 A y P s n x h1 h2 h3 h4)). Qed.
Lemma lem401610 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : (term1170 A y P m s n x) = False.
Proof. exact (prop_ext (fun h6 : term1170 A y P m s n x => @lem401609 A y P m s n x h1 h2 h3 h4 h5) (fun h6 : False => @lem399427 A y P m s n x h5)). Qed.
Lemma lem401611 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : False.
Proof. exact (EQ_MP (@lem401610 A y P m s n x h1 h2 h3 h4 h5) (@lem399427 A y P m s n x h5)). Qed.
Lemma lem401612 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : term327 = False.
Proof. exact (prop_ext (fun h6 : term327 => @lem401611 A y P m s n x h1 h2 h3 h4 h5) (fun h6 : False => @lem399373 h2)). Qed.
Lemma lem401613 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : False.
Proof. exact (EQ_MP (@lem401612 A y P m s n x h1 h2 h3 h4 h5) (@lem399373 h2)). Qed.
Lemma lem401614 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h6 : term554 A P x => @lem401613 A y P m s n x h1 h2 h3 h4 h5) (fun h6 : False => @lem399293 A P x h3)). Qed.
Lemma lem401615 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : False.
Proof. exact (EQ_MP (@lem401614 A y P m s n x h1 h2 h3 h4 h5) (@lem399293 A P x h3)). Qed.
Lemma lem401616 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h6 : term608 A s => @lem401615 A y P m s n x h1 h2 h3 h4 h5) (fun h6 : False => @lem399263 A s h1)). Qed.
Lemma lem401617 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1170 A y P m s n x) : False.
Proof. exact (EQ_MP (@lem401616 A y P m s n x h1 h2 h3 h4 h5) (@lem399263 A s h1)). Qed.
Lemma lem401618 {A : Type'} (y : A) (P : A -> Prop) (m : nat) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1170 A y P m s n x) : False.
Proof. exact (ex_elim (@lem398995 A P s x h3) (fun n' : nat => fun h0 : term766 A P s x n' => @lem401617 A y P m s n x h1 h2 h4 h5 h6)). Qed.
Lemma lem401619 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (ex_elim (@lem399156 A y P s n x h6) (fun m : nat => fun h0 : term1172 A y P s n x m => @lem401618 A y P m s n x h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem401620 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : term327 = False.
Proof. exact (prop_ext (fun h7 : term327 => @lem401619 A y P s n x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem399246 h2)). Qed.
Lemma lem401621 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401620 A y P s n x h1 h2 h3 h4 h5 h6) (@lem399246 h2)). Qed.
Lemma lem401622 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : (term782 A P s x) = False.
Proof. exact (prop_ext (fun h7 : term782 A P s x => @lem401621 A y P s n x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem398995 A P s x h3)). Qed.
Lemma lem401623 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401622 A y P s n x h1 h2 h3 h4 h5 h6) (@lem398995 A P s x h3)). Qed.
Lemma lem401624 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h7 : term554 A P x => @lem401623 A y P s n x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem398982 A P x h4)). Qed.
Lemma lem401625 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401624 A y P s n x h1 h2 h3 h4 h5 h6) (@lem398982 A P x h4)). Qed.
Lemma lem401626 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : (term608 A s) = False.
Proof. exact (prop_ext (fun h7 : term608 A s => @lem401625 A y P s n x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem398956 A s h1)). Qed.
Lemma lem401627 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term327) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401626 A y P s n x h1 h2 h3 h4 h5 h6) (@lem398956 A s h1)). Qed.
Lemma lem401628 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1020 A y P s n x) : term1058.
Proof. exact (fun h0 : term327 => @lem401627 A y P s n x h1 h0 h2 h3 h4 h5). Qed.
Lemma lem401629 : term1058 = term1059.
Proof. exact (@lem69 term327). Qed.
Lemma lem401630 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1053 A y P s n x) (h5 : term1020 A y P s n x) : term1059.
Proof. exact (EQ_MP (@lem401629) (@lem401628 A y P s n x h1 h2 h3 h4 h5)). Qed.
Lemma lem401631 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1020 A y P s n x) : term1062 A y P s n x.
Proof. exact (fun h0 : term1053 A y P s n x => @lem401630 A y P s n x h1 h2 h3 h0 h4). Qed.
Lemma lem401632 {A : Type'} (y : A) (n : nat) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) : term1064 A y P s n x.
Proof. exact (fun h0 : term1020 A y P s n x => @lem401631 A y P s n x h1 h2 h3 h0). Qed.
Lemma lem401633 {A : Type'} (y : A) (n : nat) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : term1066 A y P s n x.
Proof. exact (fun h0 : term782 A P s x => @lem401632 A y n s P x h1 h0 h2). Qed.
Lemma lem401634 {A : Type'} (y : A) (P : A -> Prop) (n : nat) (x : A) (s : type1423 A) (h1 : term608 A s) : term1068 A y P s n x.
Proof. exact (fun h0 : term554 A P x => @lem401633 A y n s P x h1 h0). Qed.
Lemma lem401635 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (n : nat) (x : A) (s : type1423 A) (h1 : term608 A s) : term1070 A g y P s n x.
Proof. exact (fun h0 : term649 A g s => @lem401634 A y P n x s h1). Qed.
Lemma lem401636 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1071 A g y P s n x.
Proof. exact (fun h0 : term608 A s => @lem401635 A g y P n x s h0). Qed.
Lemma lem401641 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1075 A y P s n x.
Proof. exact (fun g : A -> A => @lem401636 A g y P s n x). Qed.
Lemma lem401646 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1079 A P s n x.
Proof. exact (fun y : A => @lem401641 A y P s n x). Qed.
Lemma lem401651 {A : Type'} (s : type1423 A) (n : nat) (x : A) : term1083 A s n x.
Proof. exact (fun P : A -> Prop => @lem401646 A P s n x). Qed.
Lemma lem401656 {A : Type'} (n : nat) (x : A) : term1087 A n x.
Proof. exact (fun s : type1423 A => @lem401651 A s n x). Qed.
Lemma lem401661 {A : Type'} (x : A) : term1091 A x.
Proof. exact (fun n : nat => @lem401656 A n x). Qed.
Lemma lem401666 {A : Type'} : term1095 A.
Proof. exact (fun x : A => @lem401661 A x). Qed.
Lemma lem401667 {A : Type'} : term1094 A.
Proof. exact (EQ_MP (@lem398936 A) (@lem401666 A)). Qed.
Lemma lem401668 {A : Type'} (x : A) : term1193 A x.
Proof. exact (@lem401667 A x). Qed.
Lemma lem401669 {A : Type'} (x : A) : (term1193 A x) = (term1090 A x).
Proof. exact (eq_refl (term1193 A x)). Qed.
Lemma lem401670 {A : Type'} (x : A) : term1090 A x.
Proof. exact (EQ_MP (@lem401669 A x) (@lem401668 A x)). Qed.
Lemma lem401671 {A : Type'} (x : A) (n : nat) : term1194 A x n.
Proof. exact (@lem401670 A x n). Qed.
Lemma lem401672 {A : Type'} (n : nat) (x : A) : (term1194 A x n) = (term1086 A n x).
Proof. exact (eq_refl (term1194 A x n)). Qed.
Lemma lem401673 {A : Type'} (n : nat) (x : A) : term1086 A n x.
Proof. exact (EQ_MP (@lem401672 A n x) (@lem401671 A x n)). Qed.
Lemma lem401674 {A : Type'} (n : nat) (x : A) (s : type1423 A) : term1195 A n x s.
Proof. exact (@lem401673 A n x s). Qed.
Lemma lem401675 {A : Type'} (s : type1423 A) (n : nat) (x : A) : (term1195 A n x s) = (term1082 A s n x).
Proof. exact (eq_refl (term1195 A n x s)). Qed.
Lemma lem401676 {A : Type'} (s : type1423 A) (n : nat) (x : A) : term1082 A s n x.
Proof. exact (EQ_MP (@lem401675 A s n x) (@lem401674 A n x s)). Qed.
Lemma lem401677 {A : Type'} (s : type1423 A) (n : nat) (x : A) (P : A -> Prop) : term1196 A s n x P.
Proof. exact (@lem401676 A s n x P). Qed.
Lemma lem401678 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1196 A s n x P) = (term1078 A P s n x).
Proof. exact (eq_refl (term1196 A s n x P)). Qed.
Lemma lem401679 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1078 A P s n x.
Proof. exact (EQ_MP (@lem401678 A P s n x) (@lem401677 A s n x P)). Qed.
Lemma lem401680 {A : Type'} (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (y : A) : term1197 A P s n x y.
Proof. exact (@lem401679 A P s n x y). Qed.
Lemma lem401681 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1197 A P s n x y) = (term1074 A y P s n x).
Proof. exact (eq_refl (term1197 A P s n x y)). Qed.
Lemma lem401682 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1074 A y P s n x.
Proof. exact (EQ_MP (@lem401681 A y P s n x) (@lem401680 A P s n x y)). Qed.
Lemma lem401683 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (g : A -> A) : term1198 A y P s n x g.
Proof. exact (@lem401682 A y P s n x g). Qed.
Lemma lem401684 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : (term1198 A y P s n x g) = (term1054 A g y P s n x).
Proof. exact (eq_refl (term1198 A y P s n x g)). Qed.
Lemma lem401685 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1054 A g y P s n x.
Proof. exact (EQ_MP (@lem401684 A g y P s n x) (@lem401683 A y P s n x g)). Qed.
Lemma lem401687 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) : term1054 A g y P s n x.
Proof. exact (@lem398565 A g y P s n x (@lem401685 A g y P s n x)). Qed.
Lemma lem401688 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (n : nat) (x : A) (s : type1423 A) (h1 : term608 A s) : term1069 A g y P s n x.
Proof. exact (@lem401687 A g y P s n x (@lem394512 A s h1)). Qed.
Lemma lem401689 {A : Type'} (y : A) (P : A -> Prop) (n : nat) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : term1067 A y P s n x.
Proof. exact (@lem401688 A g y P n x s h1 (@lem394513 A g s h2)). Qed.
Lemma lem401690 {A : Type'} (y : A) (n : nat) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term1065 A y P s n x.
Proof. exact (@lem401689 A y P n x g s h1 h2 (@lem394333 A P x h3)). Qed.
Lemma lem401691 {A : Type'} (y : A) (n : nat) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1063 A y P s n x.
Proof. exact (@lem401690 A y n g s P x h1 h2 h4 (@lem397104 A P s x h3)). Qed.
Lemma lem401692 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1020 A y P s n x) : term1061 A y P s n x.
Proof. exact (@lem401691 A y n g s P x h1 h2 h3 h4 (@lem398423 A y P s n x h5)). Qed.
Lemma lem401693 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : term1058.
Proof. exact (@lem401692 A g y P s n x h1 h2 h3 h4 h6 (@lem398549 A y P s n x h5)). Qed.
Lemma lem401694 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (@lem401693 A g y P s n x h1 h2 h3 h4 h5 h6 (@lem91530)). Qed.
Lemma lem401695 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : (term1053 A y P s n x) = False.
Proof. exact (prop_ext (fun h7 : term1053 A y P s n x => @lem401694 A g y P s n x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem398549 A y P s n x h5)). Qed.
Lemma lem401696 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1053 A y P s n x) (h6 : term1020 A y P s n x) : False.
Proof. exact (EQ_MP (@lem401695 A g y P s n x h1 h2 h3 h4 h5 h6) (@lem398549 A y P s n x h5)). Qed.
Lemma lem401697 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1020 A y P s n x) : term1052 A y P s n x.
Proof. exact (fun h0 : term1053 A y P s n x => @lem401696 A g y P s n x h1 h2 h3 h4 h0 h5). Qed.
Lemma lem401699 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (n : nat) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1020 A y P s n x) : term1032 A y P s n x.
Proof. exact (EQ_MP (@lem398548 A y P s n x) (@lem401697 A g y P s n x h1 h2 h3 h4 h5)). Qed.
Lemma lem401700 {A : Type'} (y : A) (n : nat) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1034 A y P s n x.
Proof. exact (fun h0 : term1020 A y P s n x => @lem401699 A g y P s n x h1 h2 h3 h4 h0). Qed.
Lemma lem401705 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1038 A y P s x.
Proof. exact (fun n : nat => @lem401700 A y n g s P x h1 h2 h3 h4). Qed.
Lemma lem401706 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1040 A y P s x.
Proof. exact (conj (@lem398511 A y s P x h1 h4) (@lem401705 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem401707 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1022 A y P s x.
Proof. exact (@lem398422 A y P s x (@lem401706 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem401708 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term997 A P s y x.
Proof. exact (EQ_MP (@lem398399 A P s y x) (@lem401707 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem401710 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem401711 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1199 A y P s x) = (term1200 A y P s x).
Proof. exact (@lem401710 (term1199 A y P s x)). Qed.
Lemma lem401712 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1200 A y P s x) = (term1199 A y P s x).
Proof. exact (SYM (@lem401711 A y P s x)). Qed.
Lemma lem401713 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1201 A y P s x) : term1201 A y P s x.
Proof. exact (h1). Qed.
Lemma lem401716 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1202 A g y P s x) : term1202 A g y P s x.
Proof. exact (h1). Qed.
Lemma lem401717 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1203 A g y P s x.
Proof. exact (fun h0 : term1202 A g y P s x => @lem401716 A g y P s x h0). Qed.
Lemma lem401718 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1203 A g y P s x) : term1203 A g y P s x.
Proof. exact (h1). Qed.
Lemma lem401719 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1202 A g y P s x) : term1202 A g y P s x.
Proof. exact (h1). Qed.
Lemma lem401720 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1202 A g y P s x) (h2 : term1203 A g y P s x) : term1202 A g y P s x.
Proof. exact (@lem401718 A g y P s x h2 (@lem401719 A g y P s x h1)). Qed.
Lemma lem401721 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1202 A g y P s x) : term1204 A g y P s x.
Proof. exact (fun h0 : term1203 A g y P s x => @lem401720 A g y P s x h1 h0). Qed.
Lemma lem401722 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1203 A g y P s x) : term1203 A g y P s x.
Proof. exact (h1). Qed.
Lemma lem401723 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1202 A g y P s x) (h2 : term1203 A g y P s x) : term1202 A g y P s x.
Proof. exact (@lem401721 A g y P s x h1 (@lem401722 A g y P s x h2)). Qed.
Lemma lem401724 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1203 A g y P s x) : term1203 A g y P s x.
Proof. exact (fun h0 : term1202 A g y P s x => @lem401723 A g y P s x h0 h1). Qed.
Lemma lem401725 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1205 A g y P s x.
Proof. exact (fun h0 : term1203 A g y P s x => @lem401724 A g y P s x h0). Qed.
Lemma lem401728 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1203 A g y P s x.
Proof. exact (@lem401725 A g y P s x (@lem401717 A g y P s x)). Qed.
Lemma lem401729 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1203 A g y P s x.
Proof. exact (@lem401728 A g y P s x). Qed.
Lemma lem401837 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem401838 : term1206 = term1207.
Proof. exact (@lem401837 term1208). Qed.
Lemma lem401846 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem401847 (m : nat) : ((term1209 m) = False) = (term1210 m).
Proof. exact (@lem401846 (term1209 m)). Qed.
Lemma lem401848 : term1211 = term1212.
Proof. exact (fun_ext (fun m : nat => @lem401847 m)). Qed.
Lemma lem401849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem401850 : term1213 = term1214.
Proof. exact (MK_COMB (@lem401849) (@lem401848)). Qed.
Lemma lem401855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem401856 : term1215 = term1216.
Proof. exact (MK_COMB (@lem401855) (@lem401850)). Qed.
Lemma lem401867 : term1217 = term1217.
Proof. exact (eq_refl term1217). Qed.
Lemma lem401868 : term1208 = term1218.
Proof. exact (MK_COMB (@lem401856) (@lem401867)). Qed.
Lemma lem401871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem401872 : term1207 = term1219.
Proof. exact (MK_COMB (@lem401871) (@lem401868)). Qed.
Lemma lem401873 : term1206 = term1219.
Proof. exact (TRANS (@lem401838) (@lem401872)). Qed.
Lemma lem401874 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1220 A y P s x) = (term1220 A y P s x).
Proof. exact (eq_refl (term1220 A y P s x)). Qed.
Lemma lem401875 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1221 A y P s x) = (term1222 A y P s x).
Proof. exact (MK_COMB (@lem401874 A y P s x) (@lem401873)). Qed.
Lemma lem401878 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (eq_refl (term807 A P s x)). Qed.
Lemma lem401879 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1223 A y P s x) = (term1224 A y P s x).
Proof. exact (MK_COMB (@lem401878 A P s x) (@lem401875 A y P s x)). Qed.
Lemma lem401882 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem401883 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1225 A y P s x) = (term1226 A y P s x).
Proof. exact (MK_COMB (@lem401882 A P x) (@lem401879 A y P s x)). Qed.
Lemma lem401886 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (eq_refl (term909 A g s)). Qed.
Lemma lem401887 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1227 A g y P s x) = (term1228 A g y P s x).
Proof. exact (MK_COMB (@lem401886 A g s) (@lem401883 A y P s x)). Qed.
Lemma lem401890 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (eq_refl (term912 A s)). Qed.
Lemma lem401891 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1202 A g y P s x) = (term1229 A g y P s x).
Proof. exact (MK_COMB (@lem401890 A s) (@lem401887 A g y P s x)). Qed.
Lemma lem401894 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1230 A y P s x) = (term1231 A y P s x).
Proof. exact (fun_ext (fun g : A -> A => @lem401891 A g y P s x)). Qed.
Lemma lem401895 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem401896 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1232 A y P s x) = (term1233 A y P s x).
Proof. exact (MK_COMB (@lem401895 A) (@lem401894 A y P s x)). Qed.
Lemma lem401901 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1234 A P s x) = (term1235 A P s x).
Proof. exact (fun_ext (fun y : A => @lem401896 A y P s x)). Qed.
Lemma lem401902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem401903 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1236 A P s x) = (term1237 A P s x).
Proof. exact (MK_COMB (@lem401902 A) (@lem401901 A P s x)). Qed.
Lemma lem401908 {A : Type'} (s : type1423 A) (x : A) : (term1238 A s x) = (term1239 A s x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem401903 A P s x)). Qed.
Lemma lem401909 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem401910 {A : Type'} (s : type1423 A) (x : A) : (term1240 A s x) = (term1241 A s x).
Proof. exact (MK_COMB (@lem401909 A) (@lem401908 A s x)). Qed.
Lemma lem401915 {A : Type'} (x : A) : (term1242 A x) = (term1243 A x).
Proof. exact (fun_ext (fun s : type1423 A => @lem401910 A s x)). Qed.
Lemma lem401916 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem401917 {A : Type'} (x : A) : (term1244 A x) = (term1245 A x).
Proof. exact (MK_COMB (@lem401916 A) (@lem401915 A x)). Qed.
Lemma lem401922 {A : Type'} : (term1246 A) = (term1247 A).
Proof. exact (fun_ext (fun x : A => @lem401917 A x)). Qed.
Lemma lem401923 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem401932 {A : Type'} : (term1248 A) = (term1249 A).
Proof. exact (MK_COMB (@lem401923 A) (@lem401922 A)). Qed.
Lemma lem401941 (m : nat) (n : nat) : ((term363 m n) = (term1250 m n)) = ((term363 m n) = (term1250 m n)).
Proof. exact (eq_refl ((term363 m n) = (term1250 m n))). Qed.
Lemma lem401942 (m : nat) : (term1251 m) = (term1251 m).
Proof. exact (fun_ext (fun n : nat => @lem401941 m n)). Qed.
Lemma lem401943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem401944 (m : nat) : (term1252 m) = (term1252 m).
Proof. exact (MK_COMB (@lem401943) (@lem401942 m)). Qed.
Lemma lem401945 : term1253 = term1253.
Proof. exact (fun_ext (fun m : nat => @lem401944 m)). Qed.
Lemma lem401946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem401947 : term1217 = term1217.
Proof. exact (MK_COMB (@lem401946) (@lem401945)). Qed.
Lemma lem401950 (m : nat) : (term1210 m) = (term1210 m).
Proof. exact (eq_refl (term1210 m)). Qed.
Lemma lem401951 : term1212 = term1212.
Proof. exact (fun_ext (fun m : nat => @lem401950 m)). Qed.
Lemma lem401952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem401953 : term1214 = term1214.
Proof. exact (MK_COMB (@lem401952) (@lem401951)). Qed.
Lemma lem401954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem401955 : term1216 = term1216.
Proof. exact (MK_COMB (@lem401954) (@lem401953)). Qed.
Lemma lem401956 : term1218 = term1218.
Proof. exact (MK_COMB (@lem401955) (@lem401947)). Qed.
Lemma lem401957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem401958 : term1219 = term1219.
Proof. exact (MK_COMB (@lem401957) (@lem401956)). Qed.
Lemma lem401963 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1097 A n P s x m) = (term1097 A n P s x m).
Proof. exact (eq_refl (term1097 A n P s x m)). Qed.
Lemma lem401964 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1098 A n P s x) = (term1098 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem401963 A n P s x m)). Qed.
Lemma lem401965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem401966 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1099 A n P s x) = (term1099 A n P s x).
Proof. exact (MK_COMB (@lem401965) (@lem401964 A n P s x)). Qed.
Lemma lem401971 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1100 A P s x n) = (term1100 A P s x n).
Proof. exact (eq_refl (term1100 A P s x n)). Qed.
Lemma lem401972 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1101 A n P s x) = (term1101 A n P s x).
Proof. exact (MK_COMB (@lem401971 A P s x n) (@lem401966 A n P s x)). Qed.
Lemma lem401975 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1102 A y s x n) = (term1102 A y s x n).
Proof. exact (eq_refl (term1102 A y s x n)). Qed.
Lemma lem401976 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term867 A y n P s x) = (term867 A y n P s x).
Proof. exact (MK_COMB (@lem401975 A y s x n) (@lem401972 A n P s x)). Qed.
Lemma lem401977 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term854 A y P s x) = (term854 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem401976 A y n P s x)). Qed.
Lemma lem401978 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem401979 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term870 A y P s x) = (term870 A y P s x).
Proof. exact (MK_COMB (@lem401978) (@lem401977 A y P s x)). Qed.
Lemma lem401982 {A : Type'} (y : A) (x : A) : (term1254 A y x) = (term1254 A y x).
Proof. exact (eq_refl (term1254 A y x)). Qed.
Lemma lem401983 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1199 A y P s x) = (term1199 A y P s x).
Proof. exact (MK_COMB (@lem401982 A y x) (@lem401979 A y P s x)). Qed.
Lemma lem401984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem401985 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1201 A y P s x) = (term1201 A y P s x).
Proof. exact (MK_COMB (@lem401984) (@lem401983 A y P s x)). Qed.
Lemma lem401986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401987 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1220 A y P s x) = (term1220 A y P s x).
Proof. exact (MK_COMB (@lem401986) (@lem401985 A y P s x)). Qed.
Lemma lem401988 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1222 A y P s x) = (term1222 A y P s x).
Proof. exact (MK_COMB (@lem401987 A y P s x) (@lem401958)). Qed.
Lemma lem401991 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term779 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term779 A P s x n)). Qed.
Lemma lem401992 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term766 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem401991 A P s x n)). Qed.
Lemma lem401993 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem401994 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem401993) (@lem401992 A P s x)). Qed.
Lemma lem401995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem401996 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term807 A P s x) = (term807 A P s x).
Proof. exact (MK_COMB (@lem401995) (@lem401994 A P s x)). Qed.
Lemma lem401997 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1224 A y P s x) = (term1224 A y P s x).
Proof. exact (MK_COMB (@lem401996 A P s x) (@lem401988 A y P s x)). Qed.
Lemma lem402002 {A : Type'} (P : A -> Prop) (x : A) : (term906 A P x) = (term906 A P x).
Proof. exact (eq_refl (term906 A P x)). Qed.
Lemma lem402003 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1226 A y P s x) = (term1226 A y P s x).
Proof. exact (MK_COMB (@lem402002 A P x) (@lem401997 A y P s x)). Qed.
Lemma lem402004 {A : Type'} (g : A -> A) (s : type1423 A) (x : A) (n : nat) : ((term687 A s g x n) = (term635 A s x n)) = ((term687 A s g x n) = (term635 A s x n)).
Proof. exact (eq_refl ((term687 A s g x n) = (term635 A s x n))). Qed.
Lemma lem402005 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term938 A g s n) = (term938 A g s n).
Proof. exact (fun_ext (fun x : A => @lem402004 A g s x n)). Qed.
Lemma lem402006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402007 {A : Type'} (g : A -> A) (s : type1423 A) (n : nat) : (term657 A g s n) = (term657 A g s n).
Proof. exact (MK_COMB (@lem402006 A) (@lem402005 A g s n)). Qed.
Lemma lem402008 {A : Type'} (g : A -> A) (s : type1423 A) : (term651 A g s) = (term651 A g s).
Proof. exact (fun_ext (fun n : nat => @lem402007 A g s n)). Qed.
Lemma lem402009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402010 {A : Type'} (g : A -> A) (s : type1423 A) : (term649 A g s) = (term649 A g s).
Proof. exact (MK_COMB (@lem402009) (@lem402008 A g s)). Qed.
Lemma lem402011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem402012 {A : Type'} (g : A -> A) (s : type1423 A) : (term909 A g s) = (term909 A g s).
Proof. exact (MK_COMB (@lem402011) (@lem402010 A g s)). Qed.
Lemma lem402013 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1228 A g y P s x) = (term1228 A g y P s x).
Proof. exact (MK_COMB (@lem402012 A g s) (@lem402003 A y P s x)). Qed.
Lemma lem402014 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem402015 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem402014 A s x)). Qed.
Lemma lem402016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402017 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem402016 A) (@lem402015 A s)). Qed.
Lemma lem402018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem402019 {A : Type'} (s : type1423 A) : (term912 A s) = (term912 A s).
Proof. exact (MK_COMB (@lem402018) (@lem402017 A s)). Qed.
Lemma lem402020 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1229 A g y P s x) = (term1229 A g y P s x).
Proof. exact (MK_COMB (@lem402019 A s) (@lem402013 A g y P s x)). Qed.
Lemma lem402021 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1231 A y P s x) = (term1231 A y P s x).
Proof. exact (fun_ext (fun g : A -> A => @lem402020 A g y P s x)). Qed.
Lemma lem402022 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem402023 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1233 A y P s x) = (term1233 A y P s x).
Proof. exact (MK_COMB (@lem402022 A) (@lem402021 A y P s x)). Qed.
Lemma lem402024 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1235 A P s x) = (term1235 A P s x).
Proof. exact (fun_ext (fun y : A => @lem402023 A y P s x)). Qed.
Lemma lem402025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402026 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1237 A P s x) = (term1237 A P s x).
Proof. exact (MK_COMB (@lem402025 A) (@lem402024 A P s x)). Qed.
Lemma lem402027 {A : Type'} (s : type1423 A) (x : A) : (term1239 A s x) = (term1239 A s x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem402026 A P s x)). Qed.
Lemma lem402028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem402029 {A : Type'} (s : type1423 A) (x : A) : (term1241 A s x) = (term1241 A s x).
Proof. exact (MK_COMB (@lem402028 A) (@lem402027 A s x)). Qed.
Lemma lem402030 {A : Type'} (x : A) : (term1243 A x) = (term1243 A x).
Proof. exact (fun_ext (fun s : type1423 A => @lem402029 A s x)). Qed.
Lemma lem402031 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem402032 {A : Type'} (x : A) : (term1245 A x) = (term1245 A x).
Proof. exact (MK_COMB (@lem402031 A) (@lem402030 A x)). Qed.
Lemma lem402033 {A : Type'} : (term1247 A) = (term1247 A).
Proof. exact (fun_ext (fun x : A => @lem402032 A x)). Qed.
Lemma lem402034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402035 {A : Type'} : (term1249 A) = (term1249 A).
Proof. exact (MK_COMB (@lem402034 A) (@lem402033 A)). Qed.
Lemma lem402144 {A : Type'} : (term1248 A) = (term1249 A).
Proof. exact (TRANS (@lem401932 A) (@lem402035 A)). Qed.
Lemma lem402145 {A : Type'} : (term1249 A) = (term1248 A).
Proof. exact (SYM (@lem402144 A)). Qed.
Lemma lem402146 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (h1). Qed.
Lemma lem402149 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (h1). Qed.
Lemma lem402150 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1201 A y P s x) : term1201 A y P s x.
Proof. exact (h1). Qed.
Lemma lem402151 (h1 : term1218) : term1218.
Proof. exact (h1). Qed.
Lemma lem402152 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem402153 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem402152 A s x)). Qed.
Lemma lem402154 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402163 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem402154 A) (@lem402153 A s)). Qed.
Lemma lem402164 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem402163 A s) (@lem402146 A s h1)). Qed.
Lemma lem402190 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem402191 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term779 A P s x n) = (term779 A P s x n).
Proof. exact (eq_refl (term779 A P s x n)). Qed.
Lemma lem402192 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term766 A P s x) = (term766 A P s x).
Proof. exact (fun_ext (fun n : nat => @lem402191 A P s x n)). Qed.
Lemma lem402193 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402202 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term782 A P s x) = (term782 A P s x).
Proof. exact (MK_COMB (@lem402193) (@lem402192 A P s x)). Qed.
Lemma lem402203 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term782 A P s x) : term782 A P s x.
Proof. exact (EQ_MP (@lem402202 A P s x) (@lem402149 A P s x h1)). Qed.
Lemma lem402208 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term939 A P s x n) = (term841 A P s x n).
Proof. exact (@lem16933 (term841 A P s x n)). Qed.
Lemma lem402215 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1103 A n P s x m) = (term1104 A n P s x m).
Proof. exact (@lem17362 (Peano.lt m n) (term841 A P s x m)). Qed.
Lemma lem402216 (P : nat -> Prop) : (term1105 P) = (term1106 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem402217 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1107 A n P s x) = (term1108 A n P s x).
Proof. exact (@lem402216 (term1098 A n P s x)). Qed.
Lemma lem402218 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1109 A n P s x m) = (term1097 A n P s x m).
Proof. exact (eq_refl (term1109 A n P s x m)). Qed.
Lemma lem402219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem402220 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1110 A n P s x m) = (term1103 A n P s x m).
Proof. exact (MK_COMB (@lem402219) (@lem402218 A n P s x m)). Qed.
Lemma lem402221 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1110 A n P s x m) = (term1104 A n P s x m).
Proof. exact (TRANS (@lem402220 A n P s x m) (@lem402215 A n P s x m)). Qed.
Lemma lem402222 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1111 A n P s x) = (term1112 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402221 A n P s x m)). Qed.
Lemma lem402223 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402224 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1108 A n P s x) = (term1113 A n P s x).
Proof. exact (MK_COMB (@lem402223) (@lem402222 A n P s x)). Qed.
Lemma lem402225 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1107 A n P s x) = (term1113 A n P s x).
Proof. exact (TRANS (@lem402217 A n P s x) (@lem402224 A n P s x)). Qed.
Lemma lem402226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem402227 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1114 A P s x n) = (term1115 A P s x n).
Proof. exact (MK_COMB (@lem402226) (@lem402208 A P s x n)). Qed.
Lemma lem402228 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1116 A n P s x) = (term1117 A n P s x).
Proof. exact (MK_COMB (@lem402227 A P s x n) (@lem402225 A n P s x)). Qed.
Lemma lem402229 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1118 A n P s x) = (term1116 A n P s x).
Proof. exact (@lem17045 (term779 A P s x n) (term1099 A n P s x)). Qed.
Lemma lem402230 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1118 A n P s x) = (term1117 A n P s x).
Proof. exact (TRANS (@lem402229 A n P s x) (@lem402228 A n P s x)). Qed.
Lemma lem402232 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem402233 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1120 A y n P s x) = (term1121 A y n P s x).
Proof. exact (MK_COMB (@lem402232 A y s x n) (@lem402230 A n P s x)). Qed.
Lemma lem402234 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1122 A y n P s x) = (term1120 A y n P s x).
Proof. exact (@lem17045 (y = (s x n)) (term1101 A n P s x)). Qed.
Lemma lem402235 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1122 A y n P s x) = (term1121 A y n P s x).
Proof. exact (TRANS (@lem402234 A y n P s x) (@lem402233 A y n P s x)). Qed.
Lemma lem402236 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem402237 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1255 A y P s x) = (term1256 A y P s x).
Proof. exact (@lem402236 (term854 A y P s x)). Qed.
Lemma lem402238 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term866 A y P s x n) = (term867 A y n P s x).
Proof. exact (eq_refl (term866 A y P s x n)). Qed.
Lemma lem402239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem402240 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1257 A y P s x n) = (term1122 A y n P s x).
Proof. exact (MK_COMB (@lem402239) (@lem402238 A y n P s x)). Qed.
Lemma lem402241 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1257 A y P s x n) = (term1121 A y n P s x).
Proof. exact (TRANS (@lem402240 A y n P s x) (@lem402235 A y n P s x)). Qed.
Lemma lem402242 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1258 A y P s x) = (term1259 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem402241 A y n P s x)). Qed.
Lemma lem402243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402244 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1256 A y P s x) = (term1260 A y P s x).
Proof. exact (MK_COMB (@lem402243) (@lem402242 A y P s x)). Qed.
Lemma lem402245 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1255 A y P s x) = (term1260 A y P s x).
Proof. exact (TRANS (@lem402237 A y P s x) (@lem402244 A y P s x)). Qed.
Lemma lem402247 {A : Type'} (y : A) (x : A) : (term873 A y x) = (term873 A y x).
Proof. exact (eq_refl (term873 A y x)). Qed.
Lemma lem402248 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1261 A y P s x) = (term1262 A y P s x).
Proof. exact (MK_COMB (@lem402247 A y x) (@lem402245 A y P s x)). Qed.
Lemma lem402249 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1201 A y P s x) = (term1261 A y P s x).
Proof. exact (@lem17362 (y = x) (term870 A y P s x)). Qed.
Lemma lem402250 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1201 A y P s x) = (term1262 A y P s x).
Proof. exact (TRANS (@lem402249 A y P s x) (@lem402248 A y P s x)). Qed.
Lemma lem402349 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem402350 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem402349 nat P Q). Qed.
Lemma lem402351 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1127 A n P s x) = (term1128 A n P s x).
Proof. exact (@lem402350 (term841 A P s x n) (term1112 A n P s x)). Qed.
Lemma lem402352 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1129 A n P s x m) = (term1104 A n P s x m).
Proof. exact (eq_refl (term1129 A n P s x m)). Qed.
Lemma lem402353 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1130 A n P s x) = (term1112 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402352 A n P s x m)). Qed.
Lemma lem402354 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402355 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1131 A n P s x) = (term1113 A n P s x).
Proof. exact (MK_COMB (@lem402354) (@lem402353 A n P s x)). Qed.
Lemma lem402356 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1115 A P s x n) = (term1115 A P s x n).
Proof. exact (eq_refl (term1115 A P s x n)). Qed.
Lemma lem402357 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1127 A n P s x) = (term1117 A n P s x).
Proof. exact (MK_COMB (@lem402356 A P s x n) (@lem402355 A n P s x)). Qed.
Lemma lem402358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402359 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1132 A n P s x) = (term1133 A n P s x).
Proof. exact (MK_COMB (@lem402358) (@lem402357 A n P s x)). Qed.
Lemma lem402360 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1129 A n P s x m) = (term1104 A n P s x m).
Proof. exact (eq_refl (term1129 A n P s x m)). Qed.
Lemma lem402361 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (n : nat) : (term1115 A P s x n) = (term1115 A P s x n).
Proof. exact (eq_refl (term1115 A P s x n)). Qed.
Lemma lem402362 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1134 A n P s x m) = (term1135 A n P s x m).
Proof. exact (MK_COMB (@lem402361 A P s x n) (@lem402360 A n P s x m)). Qed.
Lemma lem402363 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1136 A n P s x) = (term1137 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402362 A n P s x m)). Qed.
Lemma lem402364 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402365 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1128 A n P s x) = (term1138 A n P s x).
Proof. exact (MK_COMB (@lem402364) (@lem402363 A n P s x)). Qed.
Lemma lem402366 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1127 A n P s x) = (term1128 A n P s x)) = ((term1117 A n P s x) = (term1138 A n P s x)).
Proof. exact (MK_COMB (@lem402359 A n P s x) (@lem402365 A n P s x)). Qed.
Lemma lem402367 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1117 A n P s x) = (term1138 A n P s x).
Proof. exact (EQ_MP (@lem402366 A n P s x) (@lem402351 A n P s x)). Qed.
Lemma lem402368 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem402369 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1121 A y n P s x) = (term1139 A y n P s x).
Proof. exact (MK_COMB (@lem402368 A y s x n) (@lem402367 A n P s x)). Qed.
Lemma lem402371 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem402372 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem402371 nat P Q). Qed.
Lemma lem402373 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1140 A y n P s x) = (term1141 A y n P s x).
Proof. exact (@lem402372 (term1142 A y s x n) (term1137 A n P s x)). Qed.
Lemma lem402374 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1143 A n P s x m) = (term1135 A n P s x m).
Proof. exact (eq_refl (term1143 A n P s x m)). Qed.
Lemma lem402375 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1144 A n P s x) = (term1137 A n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402374 A n P s x m)). Qed.
Lemma lem402376 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402377 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1145 A n P s x) = (term1138 A n P s x).
Proof. exact (MK_COMB (@lem402376) (@lem402375 A n P s x)). Qed.
Lemma lem402378 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem402379 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1140 A y n P s x) = (term1139 A y n P s x).
Proof. exact (MK_COMB (@lem402378 A y s x n) (@lem402377 A n P s x)). Qed.
Lemma lem402380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402381 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1146 A y n P s x) = (term1147 A y n P s x).
Proof. exact (MK_COMB (@lem402380) (@lem402379 A y n P s x)). Qed.
Lemma lem402382 {A : Type'} (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1143 A n P s x m) = (term1135 A n P s x m).
Proof. exact (eq_refl (term1143 A n P s x m)). Qed.
Lemma lem402383 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem402384 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1148 A y n P s x m) = (term1149 A y n P s x m).
Proof. exact (MK_COMB (@lem402383 A y s x n) (@lem402382 A n P s x m)). Qed.
Lemma lem402385 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1150 A y n P s x) = (term1151 A y n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402384 A y n P s x m)). Qed.
Lemma lem402386 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402387 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1141 A y n P s x) = (term1152 A y n P s x).
Proof. exact (MK_COMB (@lem402386) (@lem402385 A y n P s x)). Qed.
Lemma lem402388 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1140 A y n P s x) = (term1141 A y n P s x)) = ((term1139 A y n P s x) = (term1152 A y n P s x)).
Proof. exact (MK_COMB (@lem402381 A y n P s x) (@lem402387 A y n P s x)). Qed.
Lemma lem402389 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1139 A y n P s x) = (term1152 A y n P s x).
Proof. exact (EQ_MP (@lem402388 A y n P s x) (@lem402373 A y n P s x)). Qed.
Lemma lem402390 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1121 A y n P s x) = (term1152 A y n P s x).
Proof. exact (TRANS (@lem402369 A y n P s x) (@lem402389 A y n P s x)). Qed.
Lemma lem402391 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1259 A y P s x) = (term1263 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem402390 A y n P s x)). Qed.
Lemma lem402392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402393 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1260 A y P s x) = (term1264 A y P s x).
Proof. exact (MK_COMB (@lem402392) (@lem402391 A y P s x)). Qed.
Lemma lem402395 {A B : Type'} (P : type1413 A B) : (term148 A B P) = (term149 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem402396 (P : type1605) : (term150 P) = (term151 P).
Proof. exact (@lem402395 nat nat P). Qed.
Lemma lem402397 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1265 A y P s x) = (term1266 A y P s x).
Proof. exact (@lem402396 (term1267 A y P s x)). Qed.
Lemma lem402398 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1268 A y P s x n) = (term1151 A y n P s x).
Proof. exact (eq_refl (term1268 A y P s x n)). Qed.
Lemma lem402399 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem402400 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1269 A y P s x n m) = (term1161 A y n P s x m).
Proof. exact (MK_COMB (@lem402398 A y n P s x) (@lem402399 m)). Qed.
Lemma lem402401 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1161 A y n P s x m) = (term1149 A y n P s x m).
Proof. exact (eq_refl (term1161 A y n P s x m)). Qed.
Lemma lem402402 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat) : (term1269 A y P s x n m) = (term1149 A y n P s x m).
Proof. exact (TRANS (@lem402400 A y n P s x m) (@lem402401 A y n P s x m)). Qed.
Lemma lem402403 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1270 A y P s x n) = (term1151 A y n P s x).
Proof. exact (fun_ext (fun m : nat => @lem402402 A y n P s x m)). Qed.
Lemma lem402404 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem402405 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1271 A y P s x n) = (term1152 A y n P s x).
Proof. exact (MK_COMB (@lem402404) (@lem402403 A y n P s x)). Qed.
Lemma lem402406 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1272 A y P s x) = (term1263 A y P s x).
Proof. exact (fun_ext (fun n : nat => @lem402405 A y n P s x)). Qed.
Lemma lem402407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402408 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1265 A y P s x) = (term1264 A y P s x).
Proof. exact (MK_COMB (@lem402407) (@lem402406 A y P s x)). Qed.
Lemma lem402409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402410 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1273 A y P s x) = (term1274 A y P s x).
Proof. exact (MK_COMB (@lem402409) (@lem402408 A y P s x)). Qed.
Lemma lem402411 {A : Type'} (y : A) (n : nat) (P : A -> Prop) (s : type1423 A) (x : A) : (term1268 A y P s x n) = (term1151 A y n P s x).
Proof. exact (eq_refl (term1268 A y P s x n)). Qed.
Lemma lem402412 (m : nat -> nat) (n : nat) : (m n) = (m n).
Proof. exact (eq_refl (m n)). Qed.
Lemma lem402413 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1275 A y P s x m n) = (term1276 A y P s x m n).
Proof. exact (MK_COMB (@lem402411 A y n P s x) (@lem402412 m n)). Qed.
Lemma lem402414 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1276 A y P s x m n) = (term1277 A y P s x m n).
Proof. exact (eq_refl (term1276 A y P s x m n)). Qed.
Lemma lem402415 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1275 A y P s x m n) = (term1277 A y P s x m n).
Proof. exact (TRANS (@lem402413 A y P s x m n) (@lem402414 A y P s x m n)). Qed.
Lemma lem402416 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1278 A y P s x m) = (term1279 A y P s x m).
Proof. exact (fun_ext (fun n : nat => @lem402415 A y P s x m n)). Qed.
Lemma lem402417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402418 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1280 A y P s x m) = (term1281 A y P s x m).
Proof. exact (MK_COMB (@lem402417) (@lem402416 A y P s x m)). Qed.
Lemma lem402419 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1282 A y P s x) = (term1283 A y P s x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem402418 A y P s x m)). Qed.
Lemma lem402420 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem402421 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1266 A y P s x) = (term1284 A y P s x).
Proof. exact (MK_COMB (@lem402420) (@lem402419 A y P s x)). Qed.
Lemma lem402422 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1265 A y P s x) = (term1266 A y P s x)) = ((term1264 A y P s x) = (term1284 A y P s x)).
Proof. exact (MK_COMB (@lem402410 A y P s x) (@lem402421 A y P s x)). Qed.
Lemma lem402423 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1264 A y P s x) = (term1284 A y P s x).
Proof. exact (EQ_MP (@lem402422 A y P s x) (@lem402397 A y P s x)). Qed.
Lemma lem402424 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1260 A y P s x) = (term1284 A y P s x).
Proof. exact (TRANS (@lem402393 A y P s x) (@lem402423 A y P s x)). Qed.
Lemma lem402425 {A : Type'} (y : A) (x : A) : (term873 A y x) = (term873 A y x).
Proof. exact (eq_refl (term873 A y x)). Qed.
Lemma lem402426 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1262 A y P s x) = (term1285 A y P s x).
Proof. exact (MK_COMB (@lem402425 A y x) (@lem402424 A y P s x)). Qed.
Lemma lem402428 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem402429 (P : Prop) (Q : type1002) : (term1286 P Q) = (term1287 P Q).
Proof. exact (@lem402428 (nat -> nat) P Q). Qed.
Lemma lem402430 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1288 A y P s x) = (term1289 A y P s x).
Proof. exact (@lem402429 (y = x) (term1283 A y P s x)). Qed.
Lemma lem402431 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1290 A y P s x m) = (term1281 A y P s x m).
Proof. exact (eq_refl (term1290 A y P s x m)). Qed.
Lemma lem402432 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1291 A y P s x) = (term1283 A y P s x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem402431 A y P s x m)). Qed.
Lemma lem402433 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem402434 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1292 A y P s x) = (term1284 A y P s x).
Proof. exact (MK_COMB (@lem402433) (@lem402432 A y P s x)). Qed.
Lemma lem402435 {A : Type'} (y : A) (x : A) : (term873 A y x) = (term873 A y x).
Proof. exact (eq_refl (term873 A y x)). Qed.
Lemma lem402436 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1288 A y P s x) = (term1285 A y P s x).
Proof. exact (MK_COMB (@lem402435 A y x) (@lem402434 A y P s x)). Qed.
Lemma lem402437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402438 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1293 A y P s x) = (term1294 A y P s x).
Proof. exact (MK_COMB (@lem402437) (@lem402436 A y P s x)). Qed.
Lemma lem402439 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1290 A y P s x m) = (term1281 A y P s x m).
Proof. exact (eq_refl (term1290 A y P s x m)). Qed.
Lemma lem402440 {A : Type'} (y : A) (x : A) : (term873 A y x) = (term873 A y x).
Proof. exact (eq_refl (term873 A y x)). Qed.
Lemma lem402441 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1295 A y P s x m) = (term1296 A y P s x m).
Proof. exact (MK_COMB (@lem402440 A y x) (@lem402439 A y P s x m)). Qed.
Lemma lem402442 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1297 A y P s x) = (term1298 A y P s x).
Proof. exact (fun_ext (fun m : nat -> nat => @lem402441 A y P s x m)). Qed.
Lemma lem402443 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem402444 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1289 A y P s x) = (term1299 A y P s x).
Proof. exact (MK_COMB (@lem402443) (@lem402442 A y P s x)). Qed.
Lemma lem402445 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : ((term1288 A y P s x) = (term1289 A y P s x)) = ((term1285 A y P s x) = (term1299 A y P s x)).
Proof. exact (MK_COMB (@lem402438 A y P s x) (@lem402444 A y P s x)). Qed.
Lemma lem402446 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1285 A y P s x) = (term1299 A y P s x).
Proof. exact (EQ_MP (@lem402445 A y P s x) (@lem402430 A y P s x)). Qed.
Lemma lem402448 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1262 A y P s x) = (term1299 A y P s x).
Proof. exact (TRANS (@lem402426 A y P s x) (@lem402446 A y P s x)). Qed.
Lemma lem402449 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1201 A y P s x) = (term1299 A y P s x).
Proof. exact (TRANS (@lem402250 A y P s x) (@lem402448 A y P s x)). Qed.
Lemma lem402450 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term1201 A y P s x) : term1299 A y P s x.
Proof. exact (EQ_MP (@lem402449 A y P s x) (@lem402150 A y P s x h1)). Qed.
Lemma lem402451 (m : nat) : (term1210 m) = (term1210 m).
Proof. exact (eq_refl (term1210 m)). Qed.
Lemma lem402452 : term1212 = term1212.
Proof. exact (fun_ext (fun m : nat => @lem402451 m)). Qed.
Lemma lem402453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402454 : term1214 = term1214.
Proof. exact (MK_COMB (@lem402453) (@lem402452)). Qed.
Lemma lem402465 (m : nat) (n : nat) : (term1300 m n) = (term1301 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem402471 (m : nat) (n : nat) : (term1302 m n) = (term1302 m n).
Proof. exact (eq_refl (term1302 m n)). Qed.
Lemma lem402473 (m : nat) (n : nat) : (term1303 m n) = (term1303 m n).
Proof. exact (eq_refl (term1303 m n)). Qed.
Lemma lem402474 (m : nat) (n : nat) : (term1304 m n) = (term1305 m n).
Proof. exact (MK_COMB (@lem402473 m n) (@lem402465 m n)). Qed.
Lemma lem402475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402476 (m : nat) (n : nat) : (term1306 m n) = (term1307 m n).
Proof. exact (MK_COMB (@lem402475) (@lem402474 m n)). Qed.
Lemma lem402477 (m : nat) (n : nat) : (term1308 m n) = (term1309 m n).
Proof. exact (MK_COMB (@lem402476 m n) (@lem402471 m n)). Qed.
Lemma lem402478 (m : nat) (n : nat) : ((term363 m n) = (term1250 m n)) = (term1308 m n).
Proof. exact (@lem17784 (term363 m n) (term1250 m n)). Qed.
Lemma lem402479 (m : nat) (n : nat) : ((term363 m n) = (term1250 m n)) = (term1309 m n).
Proof. exact (TRANS (@lem402478 m n) (@lem402477 m n)). Qed.
Lemma lem402480 (m : nat) : (term1251 m) = (term1310 m).
Proof. exact (fun_ext (fun n : nat => @lem402479 m n)). Qed.
Lemma lem402481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402482 (m : nat) : (term1252 m) = (term1311 m).
Proof. exact (MK_COMB (@lem402481) (@lem402480 m)). Qed.
Lemma lem402483 : term1253 = term1312.
Proof. exact (fun_ext (fun m : nat => @lem402482 m)). Qed.
Lemma lem402484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402485 : term1217 = term1313.
Proof. exact (MK_COMB (@lem402484) (@lem402483)). Qed.
Lemma lem402486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402487 : term1216 = term1216.
Proof. exact (MK_COMB (@lem402486) (@lem402454)). Qed.
Lemma lem402488 : term1218 = term1314.
Proof. exact (MK_COMB (@lem402487) (@lem402485)). Qed.
Lemma lem402498 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem402499 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem402498 nat P Q). Qed.
Lemma lem402500 (m : nat) : (term1315 m) = (term1316 m).
Proof. exact (@lem402499 (term1317 m) (term1318 m)). Qed.
Lemma lem402501 (m : nat) (n : nat) : (term1319 m n) = (term1305 m n).
Proof. exact (eq_refl (term1319 m n)). Qed.
Lemma lem402502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402503 (m : nat) (n : nat) : (term1320 m n) = (term1307 m n).
Proof. exact (MK_COMB (@lem402502) (@lem402501 m n)). Qed.
Lemma lem402504 (m : nat) (n : nat) : (term1321 m n) = (term1302 m n).
Proof. exact (eq_refl (term1321 m n)). Qed.
Lemma lem402505 (m : nat) (n : nat) : (term1322 m n) = (term1309 m n).
Proof. exact (MK_COMB (@lem402503 m n) (@lem402504 m n)). Qed.
Lemma lem402506 (m : nat) : (term1323 m) = (term1310 m).
Proof. exact (fun_ext (fun n : nat => @lem402505 m n)). Qed.
Lemma lem402507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402508 (m : nat) : (term1315 m) = (term1311 m).
Proof. exact (MK_COMB (@lem402507) (@lem402506 m)). Qed.
Lemma lem402509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402510 (m : nat) : (term1324 m) = (term1325 m).
Proof. exact (MK_COMB (@lem402509) (@lem402508 m)). Qed.
Lemma lem402511 (m : nat) (n : nat) : (term1319 m n) = (term1305 m n).
Proof. exact (eq_refl (term1319 m n)). Qed.
Lemma lem402512 (m : nat) : (term1326 m) = (term1317 m).
Proof. exact (fun_ext (fun n : nat => @lem402511 m n)). Qed.
Lemma lem402513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402514 (m : nat) : (term1327 m) = (term1328 m).
Proof. exact (MK_COMB (@lem402513) (@lem402512 m)). Qed.
Lemma lem402515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402516 (m : nat) : (term1329 m) = (term1330 m).
Proof. exact (MK_COMB (@lem402515) (@lem402514 m)). Qed.
Lemma lem402517 (m : nat) (n : nat) : (term1321 m n) = (term1302 m n).
Proof. exact (eq_refl (term1321 m n)). Qed.
Lemma lem402518 (m : nat) : (term1331 m) = (term1318 m).
Proof. exact (fun_ext (fun n : nat => @lem402517 m n)). Qed.
Lemma lem402519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402520 (m : nat) : (term1332 m) = (term1333 m).
Proof. exact (MK_COMB (@lem402519) (@lem402518 m)). Qed.
Lemma lem402521 (m : nat) : (term1316 m) = (term1334 m).
Proof. exact (MK_COMB (@lem402516 m) (@lem402520 m)). Qed.
Lemma lem402522 (m : nat) : ((term1315 m) = (term1316 m)) = ((term1311 m) = (term1334 m)).
Proof. exact (MK_COMB (@lem402510 m) (@lem402521 m)). Qed.
Lemma lem402523 (m : nat) : (term1311 m) = (term1334 m).
Proof. exact (EQ_MP (@lem402522 m) (@lem402500 m)). Qed.
Lemma lem402620 : term1312 = term1335.
Proof. exact (fun_ext (fun m : nat => @lem402523 m)). Qed.
Lemma lem402621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402622 : term1313 = term1336.
Proof. exact (MK_COMB (@lem402621) (@lem402620)). Qed.
Lemma lem402624 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem402625 (P : nat -> Prop) (Q : nat -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem402624 nat P Q). Qed.
Lemma lem402626 : term1337 = term1338.
Proof. exact (@lem402625 term1339 term1340). Qed.
Lemma lem402627 (m : nat) : (term1341 m) = (term1328 m).
Proof. exact (eq_refl (term1341 m)). Qed.
Lemma lem402628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402629 (m : nat) : (term1342 m) = (term1330 m).
Proof. exact (MK_COMB (@lem402628) (@lem402627 m)). Qed.
Lemma lem402630 (m : nat) : (term1343 m) = (term1333 m).
Proof. exact (eq_refl (term1343 m)). Qed.
Lemma lem402631 (m : nat) : (term1344 m) = (term1334 m).
Proof. exact (MK_COMB (@lem402629 m) (@lem402630 m)). Qed.
Lemma lem402632 : term1345 = term1335.
Proof. exact (fun_ext (fun m : nat => @lem402631 m)). Qed.
Lemma lem402633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402634 : term1337 = term1336.
Proof. exact (MK_COMB (@lem402633) (@lem402632)). Qed.
Lemma lem402635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem402636 : term1346 = term1347.
Proof. exact (MK_COMB (@lem402635) (@lem402634)). Qed.
Lemma lem402637 (m : nat) : (term1341 m) = (term1328 m).
Proof. exact (eq_refl (term1341 m)). Qed.
Lemma lem402638 : term1348 = term1339.
Proof. exact (fun_ext (fun m : nat => @lem402637 m)). Qed.
Lemma lem402639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402640 : term1349 = term1350.
Proof. exact (MK_COMB (@lem402639) (@lem402638)). Qed.
Lemma lem402641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402642 : term1351 = term1352.
Proof. exact (MK_COMB (@lem402641) (@lem402640)). Qed.
Lemma lem402643 (m : nat) : (term1343 m) = (term1333 m).
Proof. exact (eq_refl (term1343 m)). Qed.
Lemma lem402644 : term1353 = term1340.
Proof. exact (fun_ext (fun m : nat => @lem402643 m)). Qed.
Lemma lem402645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402646 : term1354 = term1355.
Proof. exact (MK_COMB (@lem402645) (@lem402644)). Qed.
Lemma lem402647 : term1338 = term1356.
Proof. exact (MK_COMB (@lem402642) (@lem402646)). Qed.
Lemma lem402648 : (term1337 = term1338) = (term1336 = term1356).
Proof. exact (MK_COMB (@lem402636) (@lem402647)). Qed.
Lemma lem402649 : term1336 = term1356.
Proof. exact (EQ_MP (@lem402648) (@lem402626)). Qed.
Lemma lem402754 : term1313 = term1356.
Proof. exact (TRANS (@lem402622) (@lem402649)). Qed.
Lemma lem402755 : term1216 = term1216.
Proof. exact (eq_refl term1216). Qed.
Lemma lem402758 : term1314 = term1357.
Proof. exact (MK_COMB (@lem402755) (@lem402754)). Qed.
Lemma lem402759 : term1218 = term1357.
Proof. exact (TRANS (@lem402488) (@lem402758)). Qed.
Lemma lem402760 (h1 : term1218) : term1357.
Proof. exact (EQ_MP (@lem402759) (@lem402151 h1)). Qed.
Lemma lem402761 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1296 A y P s x m.
Proof. exact (h1). Qed.
Lemma lem402773 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem402774 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem402773 A s x)). Qed.
Lemma lem402775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402776 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem402775 A) (@lem402774 A s)). Qed.
Lemma lem402777 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem402776 A s) (@lem402164 A s h1)). Qed.
Lemma lem402807 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem402832 (m : nat) (n : nat) : (term1302 m n) = (term1302 m n).
Proof. exact (eq_refl (term1302 m n)). Qed.
Lemma lem402833 (m : nat) : (term1318 m) = (term1318 m).
Proof. exact (fun_ext (fun n : nat => @lem402832 m n)). Qed.
Lemma lem402834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402835 (m : nat) : (term1333 m) = (term1333 m).
Proof. exact (MK_COMB (@lem402834) (@lem402833 m)). Qed.
Lemma lem402836 : term1340 = term1340.
Proof. exact (fun_ext (fun m : nat => @lem402835 m)). Qed.
Lemma lem402837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402838 : term1355 = term1355.
Proof. exact (MK_COMB (@lem402837) (@lem402836)). Qed.
Lemma lem402865 (m : nat) (n : nat) : (term1305 m n) = (term1305 m n).
Proof. exact (eq_refl (term1305 m n)). Qed.
Lemma lem402866 (m : nat) : (term1317 m) = (term1317 m).
Proof. exact (fun_ext (fun n : nat => @lem402865 m n)). Qed.
Lemma lem402867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402868 (m : nat) : (term1328 m) = (term1328 m).
Proof. exact (MK_COMB (@lem402867) (@lem402866 m)). Qed.
Lemma lem402869 : term1339 = term1339.
Proof. exact (fun_ext (fun m : nat => @lem402868 m)). Qed.
Lemma lem402870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402871 : term1350 = term1350.
Proof. exact (MK_COMB (@lem402870) (@lem402869)). Qed.
Lemma lem402872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402873 : term1352 = term1352.
Proof. exact (MK_COMB (@lem402872) (@lem402871)). Qed.
Lemma lem402874 : term1356 = term1356.
Proof. exact (MK_COMB (@lem402873) (@lem402838)). Qed.
Lemma lem402883 (m : nat) : (term1210 m) = (term1210 m).
Proof. exact (eq_refl (term1210 m)). Qed.
Lemma lem402884 : term1212 = term1212.
Proof. exact (fun_ext (fun m : nat => @lem402883 m)). Qed.
Lemma lem402885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402886 : term1214 = term1214.
Proof. exact (MK_COMB (@lem402885) (@lem402884)). Qed.
Lemma lem402887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem402888 : term1216 = term1216.
Proof. exact (MK_COMB (@lem402887) (@lem402886)). Qed.
Lemma lem402889 : term1357 = term1357.
Proof. exact (MK_COMB (@lem402888) (@lem402874)). Qed.
Lemma lem402890 (h1 : term1218) : term1357.
Proof. exact (EQ_MP (@lem402889) (@lem402760 h1)). Qed.
Lemma lem402935 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1277 A y P s x m n) = (term1277 A y P s x m n).
Proof. exact (eq_refl (term1277 A y P s x m n)). Qed.
Lemma lem402936 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1279 A y P s x m) = (term1279 A y P s x m).
Proof. exact (fun_ext (fun n : nat => @lem402935 A y P s x m n)). Qed.
Lemma lem402937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem402938 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1281 A y P s x m) = (term1281 A y P s x m).
Proof. exact (MK_COMB (@lem402937) (@lem402936 A y P s x m)). Qed.
Lemma lem402945 {A : Type'} (y : A) (x : A) : (term873 A y x) = (term873 A y x).
Proof. exact (eq_refl (term873 A y x)). Qed.
Lemma lem402946 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1296 A y P s x m) = (term1296 A y P s x m).
Proof. exact (MK_COMB (@lem402945 A y x) (@lem402938 A y P s x m)). Qed.
Lemma lem402947 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1296 A y P s x m.
Proof. exact (EQ_MP (@lem402946 A y P s x m) (@lem402761 A y P s x m h1)). Qed.
Lemma lem402958 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1281 A y P s x m.
Proof. exact (proj2 (@lem402947 A y P s x m h1)). Qed.
Lemma lem402961 (h1 : term1218) : term1214.
Proof. exact (proj1 (@lem402890 h1)). Qed.
Lemma lem402965 {A : Type'} (s : type1423 A) (x : A) : ((term597 A s x) = x) = ((term597 A s x) = x).
Proof. exact (eq_refl ((term597 A s x) = x)). Qed.
Lemma lem402966 {A : Type'} (s : type1423 A) : (term594 A s) = (term594 A s).
Proof. exact (fun_ext (fun x : A => @lem402965 A s x)). Qed.
Lemma lem402967 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem402969 {A : Type'} (s : type1423 A) : (term608 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem402967 A) (@lem402966 A s)). Qed.
Lemma lem402970 {A : Type'} (s : type1423 A) (h1 : term608 A s) : term608 A s.
Proof. exact (EQ_MP (@lem402969 A s) (@lem402777 A s h1)). Qed.
Lemma lem402984 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem403010 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1358 A P s x m n) = (term1359 A P s x m n).
Proof. exact (@lem19490 (term1360 m n) (term841 A P s x n) (term1361 A P s x m n)). Qed.
Lemma lem403013 {A : Type'} (y : A) (s : type1423 A) (x : A) (n : nat) : (term1119 A y s x n) = (term1119 A y s x n).
Proof. exact (eq_refl (term1119 A y s x n)). Qed.
Lemma lem403014 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1277 A y P s x m n) = (term1362 A y P s x m n).
Proof. exact (MK_COMB (@lem403013 A y s x n) (@lem403010 A P s x m n)). Qed.
Lemma lem403021 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1362 A y P s x m n) = (term1363 A y P s x m n).
Proof. exact (@lem19490 (term1364 A P s x m n) (term1142 A y s x n) (term1365 A P s x m n)). Qed.
Lemma lem403022 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (n : nat) : (term1277 A y P s x m n) = (term1363 A y P s x m n).
Proof. exact (TRANS (@lem403014 A y P s x m n) (@lem403021 A y P s x m n)). Qed.
Lemma lem403023 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1279 A y P s x m) = (term1366 A y P s x m).
Proof. exact (fun_ext (fun n : nat => @lem403022 A y P s x m n)). Qed.
Lemma lem403024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem403026 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) : (term1281 A y P s x m) = (term1367 A y P s x m).
Proof. exact (MK_COMB (@lem403024) (@lem403023 A y P s x m)). Qed.
Lemma lem403027 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1367 A y P s x m.
Proof. exact (EQ_MP (@lem403026 A y P s x m) (@lem402958 A y P s x m h1)). Qed.
Lemma lem403029 (m : nat) : (term1210 m) = (term1210 m).
Proof. exact (eq_refl (term1210 m)). Qed.
Lemma lem403030 : term1212 = term1212.
Proof. exact (fun_ext (fun m : nat => @lem403029 m)). Qed.
Lemma lem403031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem403033 : term1214 = term1214.
Proof. exact (MK_COMB (@lem403031) (@lem403030)). Qed.
Lemma lem403034 (h1 : term1218) : term1214.
Proof. exact (EQ_MP (@lem403033) (@lem402961 h1)). Qed.
Lemma lem403083 {A : Type'} (_8522 : A) (s : type1423 A) (h1 : term608 A s) : term596 A s _8522.
Proof. exact (@lem402970 A s h1 _8522). Qed.
Lemma lem403084 {A : Type'} (s : type1423 A) (_8522 : A) : (term596 A s _8522) = ((term597 A s _8522) = _8522).
Proof. exact (eq_refl (term596 A s _8522)). Qed.
Lemma lem403092 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1368 A y P s x m _8525.
Proof. exact (@lem403027 A y P s x m h1 _8525). Qed.
Lemma lem403093 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1368 A y P s x m _8525) = (term1363 A y P s x m _8525).
Proof. exact (eq_refl (term1368 A y P s x m _8525)). Qed.
Lemma lem403094 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1363 A y P s x m _8525.
Proof. exact (EQ_MP (@lem403093 A y P s x m _8525) (@lem403092 A _8525 y P s x m h1)). Qed.
Lemma lem403095 (_8526 : nat) (h1 : term1218) : term1369 _8526.
Proof. exact (@lem403034 h1 _8526). Qed.
Lemma lem403096 (_8526 : nat) : (term1369 _8526) = (term1210 _8526).
Proof. exact (eq_refl (term1369 _8526)). Qed.
Lemma lem403119 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem403123 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : y = x.
Proof. exact (proj1 (@lem402947 A y P s x m h1)). Qed.
Lemma lem403157 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1370 A y P s x m _8525.
Proof. exact (proj1 (@lem403094 A _8525 y P s x m h1)). Qed.
Lemma lem403223 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term554 A P x.
Proof. exact (h1). Qed.
Lemma lem403294 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1371 A P s x m _8525) = (term1371 A P s x m _8525).
Proof. exact (eq_refl (term1371 A P s x m _8525)). Qed.
Lemma lem403295 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : (term1372 A P s x m _8525 y) = (term1373 A P s m _8525 x).
Proof. exact (MK_COMB (@lem403294 A P s x m _8525) (@lem403123 A y P s x m h1)). Qed.
Lemma lem403296 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1373 A P s m _8525 x) = (term1374 A P s x m _8525).
Proof. exact (eq_refl (term1373 A P s m _8525 x)). Qed.
Lemma lem403297 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) (y : A) : (term1375 A P s x m _8525 y) = (term1375 A P s x m _8525 y).
Proof. exact (eq_refl (term1375 A P s x m _8525 y)). Qed.
Lemma lem403298 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : ((term1372 A P s x m _8525 y) = (term1373 A P s m _8525 x)) = ((term1372 A P s x m _8525 y) = (term1374 A P s x m _8525)).
Proof. exact (MK_COMB (@lem403297 A P s x m _8525 y) (@lem403296 A P s x m _8525)). Qed.
Lemma lem403299 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1372 A P s x m _8525 y) = (term1370 A y P s x m _8525).
Proof. exact (eq_refl (term1372 A P s x m _8525 y)). Qed.
Lemma lem403300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem403301 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1375 A P s x m _8525 y) = (term1376 A y P s x m _8525).
Proof. exact (MK_COMB (@lem403300) (@lem403299 A y P s x m _8525)). Qed.
Lemma lem403302 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1374 A P s x m _8525) = (term1374 A P s x m _8525).
Proof. exact (eq_refl (term1374 A P s x m _8525)). Qed.
Lemma lem403303 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : ((term1372 A P s x m _8525 y) = (term1374 A P s x m _8525)) = ((term1370 A y P s x m _8525) = (term1374 A P s x m _8525)).
Proof. exact (MK_COMB (@lem403301 A y P s x m _8525) (@lem403302 A P s x m _8525)). Qed.
Lemma lem403304 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : ((term1372 A P s x m _8525 y) = (term1373 A P s m _8525 x)) = ((term1370 A y P s x m _8525) = (term1374 A P s x m _8525)).
Proof. exact (TRANS (@lem403298 A y P s x m _8525) (@lem403303 A y P s x m _8525)). Qed.
Lemma lem403305 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : (term1370 A y P s x m _8525) = (term1374 A P s x m _8525).
Proof. exact (EQ_MP (@lem403304 A y P s x m _8525) (@lem403295 A _8525 y P s x m h1)). Qed.
Lemma lem403306 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1374 A P s x m _8525.
Proof. exact (EQ_MP (@lem403305 A _8525 y P s x m h1) (@lem403157 A _8525 y P s x m h1)). Qed.
Lemma lem403339 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem403340 {A : Type'} (_8557 : A) (_8558 : A) (h1 : _8557 = _8558) : _8557 = _8558.
Proof. exact (h1). Qed.
Lemma lem403341 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) (h1 : _8557 = _8558) : (P _8557) = (P _8558).
Proof. exact (MK_COMB (@lem403339 A P) (@lem403340 A _8557 _8558 h1)). Qed.
Lemma lem403343 (b : Prop) (a : Prop) : term181 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem403344 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : term944 A _8558 P _8557.
Proof. exact (@lem403343 (P _8558) (P _8557)). Qed.
Lemma lem403345 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) (h1 : _8557 = _8558) : term945 A _8558 P _8557.
Proof. exact (@lem403344 A _8558 P _8557 (@lem403341 A P _8557 _8558 h1)). Qed.
Lemma lem403346 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : term946 A _8558 P _8557.
Proof. exact (fun h0 : _8557 = _8558 => @lem403345 A P _8557 _8558 h0). Qed.
Lemma lem403348 (a : Prop) (b : Prop) : (a -> b) = (term185 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem403349 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term946 A _8558 P _8557) = (term947 A _8558 P _8557).
Proof. exact (@lem403348 (_8557 = _8558) (term945 A _8558 P _8557)). Qed.
Lemma lem403350 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : term947 A _8558 P _8557.
Proof. exact (EQ_MP (@lem403349 A _8558 P _8557) (@lem403346 A _8558 P _8557)). Qed.
Lemma lem403399 {A : Type'} (x : A) (y : A) (z : A) : term1377 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem403403 {A : Type'} (_8522 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8522) = _8522.
Proof. exact (EQ_MP (@lem403084 A s _8522) (@lem403083 A _8522 s h1)). Qed.
Lemma lem403404 {A : Type'} (_8522 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8522) = _8522.
Proof. exact (@lem403403 A _8522 s h1). Qed.
Lemma lem403405 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem403404 A x s h1). Qed.
Lemma lem403406 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem403405 A x s h1). Qed.
Lemma lem403408 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403409 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem403408 ((term597 A s x) = x)). Qed.
Lemma lem403410 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem403409 A s x) (@lem403406 A x s h1)). Qed.
Lemma lem403412 {A : Type'} (_8522 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8522) = _8522.
Proof. exact (EQ_MP (@lem403084 A s _8522) (@lem403083 A _8522 s h1)). Qed.
Lemma lem403413 {A : Type'} (_8522 : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s _8522) = _8522.
Proof. exact (@lem403412 A _8522 s h1). Qed.
Lemma lem403414 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (@lem403413 A x s h1). Qed.
Lemma lem403415 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term948 A s x.
Proof. exact (fun h0 : term949 A s x => @lem403414 A x s h1). Qed.
Lemma lem403417 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403418 {A : Type'} (s : type1423 A) (x : A) : (term948 A s x) = ((term597 A s x) = x).
Proof. exact (@lem403417 ((term597 A s x) = x)). Qed.
Lemma lem403419 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : (term597 A s x) = x.
Proof. exact (EQ_MP (@lem403418 A s x) (@lem403415 A x s h1)). Qed.
Lemma lem403421 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem403422 {A : Type'} (x : A) : x = x.
Proof. exact (@lem403421 A x). Qed.
Lemma lem403423 {A : Type'} (s : type1423 A) (x : A) : (term597 A s x) = (term597 A s x).
Proof. exact (@lem403422 A (term597 A s x)). Qed.
Lemma lem403424 {A : Type'} (s : type1423 A) (x : A) : term1378 A s x.
Proof. exact (fun h0 : term1379 A s x => @lem403423 A s x). Qed.
Lemma lem403426 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403427 {A : Type'} (s : type1423 A) (x : A) : (term1378 A s x) = ((term597 A s x) = (term597 A s x)).
Proof. exact (@lem403426 ((term597 A s x) = (term597 A s x))). Qed.
Lemma lem403428 {A : Type'} (s : type1423 A) (x : A) : (term597 A s x) = (term597 A s x).
Proof. exact (EQ_MP (@lem403427 A s x) (@lem403424 A s x)). Qed.
Lemma lem403446 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem403447 {A : Type'} (y : A) (x : A) (z : A) : (term1380 A x y z) = (term1381 A y x z).
Proof. exact (@lem403446 (y = z) (term952 A x z)). Qed.
Lemma lem403457 {A : Type'} (x : A) (y : A) : (term1382 A x y) = (term1382 A x y).
Proof. exact (eq_refl (term1382 A x y)). Qed.
Lemma lem403458 {A : Type'} (y : A) (x : A) (z : A) : (term1377 A x y z) = (term1383 A y x z).
Proof. exact (MK_COMB (@lem403457 A x y) (@lem403447 A y x z)). Qed.
Lemma lem403462 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem403463 {A : Type'} (y : A) (x : A) (z : A) : (term1383 A y x z) = (term1384 A y x z).
Proof. exact (@lem403462 (y = z) (term952 A x y) (term952 A x z)). Qed.
Lemma lem403485 {A : Type'} (y : A) (x : A) (z : A) : (term1377 A x y z) = (term1384 A y x z).
Proof. exact (TRANS (@lem403458 A y x z) (@lem403463 A y x z)). Qed.
Lemma lem403486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem403487 {A : Type'} (y : A) (x : A) (z : A) : (term1385 A x y z) = (term1386 A y x z).
Proof. exact (MK_COMB (@lem403486) (@lem403485 A y x z)). Qed.
Lemma lem403509 {A : Type'} (y : A) (x : A) (z : A) : (term1384 A y x z) = (term1384 A y x z).
Proof. exact (eq_refl (term1384 A y x z)). Qed.
Lemma lem403510 {A : Type'} (y : A) (x : A) (z : A) : ((term1377 A x y z) = (term1384 A y x z)) = ((term1384 A y x z) = (term1384 A y x z)).
Proof. exact (MK_COMB (@lem403487 A y x z) (@lem403509 A y x z)). Qed.
Lemma lem403512 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem403513 (x : Prop) : (x = x) = True.
Proof. exact (@lem403512 Prop x). Qed.
Lemma lem403514 {A : Type'} (y : A) (x : A) (z : A) : ((term1384 A y x z) = (term1384 A y x z)) = True.
Proof. exact (@lem403513 (term1384 A y x z)). Qed.
Lemma lem403515 {A : Type'} (y : A) (x : A) (z : A) : ((term1377 A x y z) = (term1384 A y x z)) = True.
Proof. exact (TRANS (@lem403510 A y x z) (@lem403514 A y x z)). Qed.
Lemma lem403516 {A : Type'} (y : A) (x : A) (z : A) : True = ((term1377 A x y z) = (term1384 A y x z)).
Proof. exact (SYM (@lem403515 A y x z)). Qed.
Lemma lem403517 {A : Type'} (y : A) (x : A) (z : A) : (term1377 A x y z) = (term1384 A y x z).
Proof. exact (EQ_MP (@lem403516 A y x z) (@lem0)). Qed.
Lemma lem403518 {A : Type'} (y : A) (x : A) (z : A) : term1384 A y x z.
Proof. exact (EQ_MP (@lem403517 A y x z) (@lem403399 A x y z)). Qed.
Lemma lem403520 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem403521 {A : Type'} (x : A) (y : A) (z : A) : (term1384 A y x z) = (term1387 A x y z).
Proof. exact (@lem403520 (term1388 A y x z) (y = z)). Qed.
Lemma lem403523 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem403524 {A : Type'} (y : A) (x : A) (z : A) : (term1389 A y x z) = (term1390 A y x z).
Proof. exact (@lem403523 (term952 A x y) (term952 A x z)). Qed.
Lemma lem403526 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem403527 {A : Type'} (x : A) (y : A) : (term962 A x y) = (x = y).
Proof. exact (@lem403526 (x = y)). Qed.
Lemma lem403528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem403529 {A : Type'} (x : A) (y : A) : (term963 A x y) = (term873 A x y).
Proof. exact (MK_COMB (@lem403528) (@lem403527 A x y)). Qed.
Lemma lem403531 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem403532 {A : Type'} (x : A) (z : A) : (term962 A x z) = (x = z).
Proof. exact (@lem403531 (x = z)). Qed.
Lemma lem403533 {A : Type'} (y : A) (x : A) (z : A) : (term1390 A y x z) = (term1391 A y x z).
Proof. exact (MK_COMB (@lem403529 A x y) (@lem403532 A x z)). Qed.
Lemma lem403534 {A : Type'} (y : A) (x : A) (z : A) : (term1389 A y x z) = (term1391 A y x z).
Proof. exact (TRANS (@lem403524 A y x z) (@lem403533 A y x z)). Qed.
Lemma lem403535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem403536 {A : Type'} (y : A) (x : A) (z : A) : (term1392 A y x z) = (term1393 A y x z).
Proof. exact (MK_COMB (@lem403535) (@lem403534 A y x z)). Qed.
Lemma lem403537 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem403538 {A : Type'} (x : A) (y : A) (z : A) : (term1387 A x y z) = (term1394 A x y z).
Proof. exact (MK_COMB (@lem403536 A y x z) (@lem403537 A y z)). Qed.
Lemma lem403539 {A : Type'} (x : A) (y : A) (z : A) : (term1384 A y x z) = (term1394 A x y z).
Proof. exact (TRANS (@lem403521 A x y z) (@lem403538 A x y z)). Qed.
Lemma lem403541 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term1395 A s x.
Proof. exact (conj (@lem403419 A x s h1) (@lem403428 A s x)). Qed.
Lemma lem403543 {A : Type'} (x : A) (y : A) (z : A) : term1394 A x y z.
Proof. exact (EQ_MP (@lem403539 A x y z) (@lem403518 A y x z)). Qed.
Lemma lem403544 {A : Type'} (x : A) (y : A) (z : A) : term1394 A x y z.
Proof. exact (@lem403543 A x y z). Qed.
Lemma lem403545 {A : Type'} (s : type1423 A) (x : A) : term1396 A s x.
Proof. exact (@lem403544 A (term597 A s x) x (term597 A s x)). Qed.
Lemma lem403548 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : x = (term597 A s x).
Proof. exact (@lem403545 A s x (@lem403541 A x s h1)). Qed.
Lemma lem403549 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : x = (term597 A s x).
Proof. exact (@lem403548 A x s h1). Qed.
Lemma lem403550 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : term1397 A s x.
Proof. exact (fun h0 : term1398 A s x => @lem403549 A x s h1). Qed.
Lemma lem403552 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403553 {A : Type'} (s : type1423 A) (x : A) : (term1397 A s x) = (x = (term597 A s x)).
Proof. exact (@lem403552 (x = (term597 A s x))). Qed.
Lemma lem403554 {A : Type'} (x : A) (s : type1423 A) (h1 : term608 A s) : x = (term597 A s x).
Proof. exact (EQ_MP (@lem403553 A s x) (@lem403550 A x s h1)). Qed.
Lemma lem403556 (_8526 : nat) (h1 : term1218) : term1210 _8526.
Proof. exact (EQ_MP (@lem403096 _8526) (@lem403095 _8526 h1)). Qed.
Lemma lem403557 (m : nat -> nat) (h1 : term1218) : term1399 m.
Proof. exact (@lem403556 (term1400 m) h1). Qed.
Lemma lem403558 (m : nat -> nat) (h1 : term1218) : term1401 m.
Proof. exact (fun h0 : term1402 m => @lem403557 m h1). Qed.
Lemma lem403560 (p : Prop) : (term189 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem403561 (m : nat -> nat) : (term1401 m) = (term1399 m).
Proof. exact (@lem403560 (term1402 m)). Qed.
Lemma lem403562 (m : nat -> nat) (h1 : term1218) : term1399 m.
Proof. exact (EQ_MP (@lem403561 m) (@lem403558 m h1)). Qed.
Lemma lem403568 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem403569 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1374 A P s x m _8525) = (term1403 A P s x m _8525).
Proof. exact (@lem403568 (term841 A P s x _8525) (term1404 A s x _8525) (term1360 m _8525)). Qed.
Lemma lem403583 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem403584 {A : Type'} (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1405 A s x m _8525) = (term1406 A m s x _8525).
Proof. exact (@lem403583 (term1360 m _8525) (term1404 A s x _8525)). Qed.
Lemma lem403592 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term1115 A P s x _8525) = (term1115 A P s x _8525).
Proof. exact (eq_refl (term1115 A P s x _8525)). Qed.
Lemma lem403593 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1403 A P s x m _8525) = (term1407 A P m s x _8525).
Proof. exact (MK_COMB (@lem403592 A P s x _8525) (@lem403584 A m s x _8525)). Qed.
Lemma lem403604 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1374 A P s x m _8525) = (term1407 A P m s x _8525).
Proof. exact (TRANS (@lem403569 A P s x m _8525) (@lem403593 A P m s x _8525)). Qed.
Lemma lem403605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem403606 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1408 A P s x m _8525) = (term1409 A P m s x _8525).
Proof. exact (MK_COMB (@lem403605) (@lem403604 A P m s x _8525)). Qed.
Lemma lem403620 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem403621 {A : Type'} (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1405 A s x m _8525) = (term1406 A m s x _8525).
Proof. exact (@lem403620 (term1360 m _8525) (term1404 A s x _8525)). Qed.
Lemma lem403629 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term1115 A P s x _8525) = (term1115 A P s x _8525).
Proof. exact (eq_refl (term1115 A P s x _8525)). Qed.
Lemma lem403630 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : (term1403 A P s x m _8525) = (term1407 A P m s x _8525).
Proof. exact (MK_COMB (@lem403629 A P s x _8525) (@lem403621 A m s x _8525)). Qed.
Lemma lem403641 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : ((term1374 A P s x m _8525) = (term1403 A P s x m _8525)) = ((term1407 A P m s x _8525) = (term1407 A P m s x _8525)).
Proof. exact (MK_COMB (@lem403606 A P m s x _8525) (@lem403630 A P m s x _8525)). Qed.
Lemma lem403643 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem403644 (x : Prop) : (x = x) = True.
Proof. exact (@lem403643 Prop x). Qed.
Lemma lem403645 {A : Type'} (P : A -> Prop) (m : nat -> nat) (s : type1423 A) (x : A) (_8525 : nat) : ((term1407 A P m s x _8525) = (term1407 A P m s x _8525)) = True.
Proof. exact (@lem403644 (term1407 A P m s x _8525)). Qed.
Lemma lem403646 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : ((term1374 A P s x m _8525) = (term1403 A P s x m _8525)) = True.
Proof. exact (TRANS (@lem403641 A P m s x _8525) (@lem403645 A P m s x _8525)). Qed.
Lemma lem403647 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : True = ((term1374 A P s x m _8525) = (term1403 A P s x m _8525)).
Proof. exact (SYM (@lem403646 A P s x m _8525)). Qed.
Lemma lem403648 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1374 A P s x m _8525) = (term1403 A P s x m _8525).
Proof. exact (EQ_MP (@lem403647 A P s x m _8525) (@lem0)). Qed.
Lemma lem403649 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1403 A P s x m _8525.
Proof. exact (EQ_MP (@lem403648 A P s x m _8525) (@lem403306 A _8525 y P s x m h1)). Qed.
Lemma lem403651 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem403652 {A : Type'} (m : nat -> nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term1403 A P s x m _8525) = (term1410 A m P s x _8525).
Proof. exact (@lem403651 (term1405 A s x m _8525) (term841 A P s x _8525)). Qed.
Lemma lem403654 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem403655 {A : Type'} (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1411 A s x m _8525) = (term1412 A s x m _8525).
Proof. exact (@lem403654 (term1404 A s x _8525) (term1360 m _8525)). Qed.
Lemma lem403657 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem403658 {A : Type'} (s : type1423 A) (x : A) (_8525 : nat) : (term1413 A s x _8525) = (x = (s x _8525)).
Proof. exact (@lem403657 (x = (s x _8525))). Qed.
Lemma lem403659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem403660 {A : Type'} (s : type1423 A) (x : A) (_8525 : nat) : (term1414 A s x _8525) = (term1415 A s x _8525).
Proof. exact (MK_COMB (@lem403659) (@lem403658 A s x _8525)). Qed.
Lemma lem403661 (m : nat -> nat) (_8525 : nat) : (term1416 m _8525) = (term1416 m _8525).
Proof. exact (eq_refl (term1416 m _8525)). Qed.
Lemma lem403662 {A : Type'} (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1412 A s x m _8525) = (term1417 A s x m _8525).
Proof. exact (MK_COMB (@lem403660 A s x _8525) (@lem403661 m _8525)). Qed.
Lemma lem403663 {A : Type'} (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1411 A s x m _8525) = (term1417 A s x m _8525).
Proof. exact (TRANS (@lem403655 A s x m _8525) (@lem403662 A s x m _8525)). Qed.
Lemma lem403664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem403665 {A : Type'} (s : type1423 A) (x : A) (m : nat -> nat) (_8525 : nat) : (term1418 A s x m _8525) = (term1419 A s x m _8525).
Proof. exact (MK_COMB (@lem403664) (@lem403663 A s x m _8525)). Qed.
Lemma lem403666 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term841 A P s x _8525) = (term841 A P s x _8525).
Proof. exact (eq_refl (term841 A P s x _8525)). Qed.
Lemma lem403667 {A : Type'} (m : nat -> nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term1410 A m P s x _8525) = (term1420 A m P s x _8525).
Proof. exact (MK_COMB (@lem403665 A s x m _8525) (@lem403666 A P s x _8525)). Qed.
Lemma lem403668 {A : Type'} (m : nat -> nat) (P : A -> Prop) (s : type1423 A) (x : A) (_8525 : nat) : (term1403 A P s x m _8525) = (term1420 A m P s x _8525).
Proof. exact (TRANS (@lem403652 A m P s x _8525) (@lem403667 A m P s x _8525)). Qed.
Lemma lem403670 {A : Type'} (x : A) (m : nat -> nat) (s : type1423 A) (h1 : term608 A s) (h2 : term1218) : term1421 A s x m.
Proof. exact (conj (@lem403554 A x s h1) (@lem403562 m h2)). Qed.
Lemma lem403672 {A : Type'} (_8525 : nat) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1420 A m P s x _8525.
Proof. exact (EQ_MP (@lem403668 A m P s x _8525) (@lem403649 A _8525 y P s x m h1)). Qed.
Lemma lem403673 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term1296 A y P s x m) : term1422 A m P s x.
Proof. exact (@lem403672 A (NUMERAL 0) y P s x m h1). Qed.
Lemma lem403676 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : term784 A P s x.
Proof. exact (@lem403673 A y P s x m h3 (@lem403670 A x m s h1 h2)). Qed.
Lemma lem403677 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : term950 A P s x.
Proof. exact (fun h0 : term768 A P s x => @lem403676 A y P s x m h1 h2 h3). Qed.
Lemma lem403679 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403680 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term950 A P s x) = (term784 A P s x).
Proof. exact (@lem403679 (term784 A P s x)). Qed.
Lemma lem403681 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : term784 A P s x.
Proof. exact (EQ_MP (@lem403680 A P s x) (@lem403677 A y P s x m h1 h2 h3)). Qed.
Lemma lem403687 (q : Prop) (p : Prop) (r : Prop) : (term215 p q r) = (term215 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem403688 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term947 A _8558 P _8557) = (term951 A _8558 P _8557).
Proof. exact (@lem403687 (P _8558) (term952 A _8557 _8558) (term554 A P _8557)). Qed.
Lemma lem403702 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem403703 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term953 A _8558 P _8557) = (term954 A P _8557 _8558).
Proof. exact (@lem403702 (term554 A P _8557) (term952 A _8557 _8558)). Qed.
Lemma lem403711 {A : Type'} (P : A -> Prop) (_8558 : A) : (term955 A P _8558) = (term955 A P _8558).
Proof. exact (eq_refl (term955 A P _8558)). Qed.
Lemma lem403712 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term951 A _8558 P _8557) = (term956 A P _8557 _8558).
Proof. exact (MK_COMB (@lem403711 A P _8558) (@lem403703 A P _8557 _8558)). Qed.
Lemma lem403723 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term947 A _8558 P _8557) = (term956 A P _8557 _8558).
Proof. exact (TRANS (@lem403688 A _8558 P _8557) (@lem403712 A P _8557 _8558)). Qed.
Lemma lem403724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem403725 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term957 A _8558 P _8557) = (term958 A P _8557 _8558).
Proof. exact (MK_COMB (@lem403724) (@lem403723 A P _8557 _8558)). Qed.
Lemma lem403739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem403740 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term953 A _8558 P _8557) = (term954 A P _8557 _8558).
Proof. exact (@lem403739 (term554 A P _8557) (term952 A _8557 _8558)). Qed.
Lemma lem403748 {A : Type'} (P : A -> Prop) (_8558 : A) : (term955 A P _8558) = (term955 A P _8558).
Proof. exact (eq_refl (term955 A P _8558)). Qed.
Lemma lem403749 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : (term951 A _8558 P _8557) = (term956 A P _8557 _8558).
Proof. exact (MK_COMB (@lem403748 A P _8558) (@lem403740 A P _8557 _8558)). Qed.
Lemma lem403760 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : ((term947 A _8558 P _8557) = (term951 A _8558 P _8557)) = ((term956 A P _8557 _8558) = (term956 A P _8557 _8558)).
Proof. exact (MK_COMB (@lem403725 A P _8557 _8558) (@lem403749 A P _8557 _8558)). Qed.
Lemma lem403762 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem403763 (x : Prop) : (x = x) = True.
Proof. exact (@lem403762 Prop x). Qed.
Lemma lem403764 {A : Type'} (P : A -> Prop) (_8557 : A) (_8558 : A) : ((term956 A P _8557 _8558) = (term956 A P _8557 _8558)) = True.
Proof. exact (@lem403763 (term956 A P _8557 _8558)). Qed.
Lemma lem403765 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : ((term947 A _8558 P _8557) = (term951 A _8558 P _8557)) = True.
Proof. exact (TRANS (@lem403760 A P _8557 _8558) (@lem403764 A P _8557 _8558)). Qed.
Lemma lem403766 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : True = ((term947 A _8558 P _8557) = (term951 A _8558 P _8557)).
Proof. exact (SYM (@lem403765 A _8558 P _8557)). Qed.
Lemma lem403767 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term947 A _8558 P _8557) = (term951 A _8558 P _8557).
Proof. exact (EQ_MP (@lem403766 A _8558 P _8557) (@lem0)). Qed.
Lemma lem403768 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : term951 A _8558 P _8557.
Proof. exact (EQ_MP (@lem403767 A _8558 P _8557) (@lem403350 A _8558 P _8557)). Qed.
Lemma lem403770 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem403771 {A : Type'} (_8557 : A) (P : A -> Prop) (_8558 : A) : (term951 A _8558 P _8557) = (term959 A _8557 P _8558).
Proof. exact (@lem403770 (term953 A _8558 P _8557) (P _8558)). Qed.
Lemma lem403773 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem403774 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term960 A _8558 P _8557) = (term961 A _8558 P _8557).
Proof. exact (@lem403773 (term952 A _8557 _8558) (term554 A P _8557)). Qed.
Lemma lem403776 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem403777 {A : Type'} (_8557 : A) (_8558 : A) : (term962 A _8557 _8558) = (_8557 = _8558).
Proof. exact (@lem403776 (_8557 = _8558)). Qed.
Lemma lem403778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem403779 {A : Type'} (_8557 : A) (_8558 : A) : (term963 A _8557 _8558) = (term873 A _8557 _8558).
Proof. exact (MK_COMB (@lem403778) (@lem403777 A _8557 _8558)). Qed.
Lemma lem403781 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem403782 {A : Type'} (P : A -> Prop) (_8557 : A) : (term964 A P _8557) = (P _8557).
Proof. exact (@lem403781 (P _8557)). Qed.
Lemma lem403783 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term961 A _8558 P _8557) = (term965 A _8558 P _8557).
Proof. exact (MK_COMB (@lem403779 A _8557 _8558) (@lem403782 A P _8557)). Qed.
Lemma lem403784 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term960 A _8558 P _8557) = (term965 A _8558 P _8557).
Proof. exact (TRANS (@lem403774 A _8558 P _8557) (@lem403783 A _8558 P _8557)). Qed.
Lemma lem403785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem403786 {A : Type'} (_8558 : A) (P : A -> Prop) (_8557 : A) : (term966 A _8558 P _8557) = (term967 A _8558 P _8557).
Proof. exact (MK_COMB (@lem403785) (@lem403784 A _8558 P _8557)). Qed.
Lemma lem403787 {A : Type'} (P : A -> Prop) (_8558 : A) : (P _8558) = (P _8558).
Proof. exact (eq_refl (P _8558)). Qed.
Lemma lem403788 {A : Type'} (_8557 : A) (P : A -> Prop) (_8558 : A) : (term959 A _8557 P _8558) = (term968 A _8557 P _8558).
Proof. exact (MK_COMB (@lem403786 A _8558 P _8557) (@lem403787 A P _8558)). Qed.
Lemma lem403789 {A : Type'} (_8557 : A) (P : A -> Prop) (_8558 : A) : (term951 A _8558 P _8557) = (term968 A _8557 P _8558).
Proof. exact (TRANS (@lem403771 A _8557 P _8558) (@lem403788 A _8557 P _8558)). Qed.
Lemma lem403791 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : term969 A P s x.
Proof. exact (conj (@lem403410 A x s h1) (@lem403681 A y P s x m h1 h2 h3)). Qed.
Lemma lem403793 {A : Type'} (_8557 : A) (P : A -> Prop) (_8558 : A) : term968 A _8557 P _8558.
Proof. exact (EQ_MP (@lem403789 A _8557 P _8558) (@lem403768 A _8558 P _8557)). Qed.
Lemma lem403794 {A : Type'} (_8557 : A) (P : A -> Prop) (_8558 : A) : term968 A _8557 P _8558.
Proof. exact (@lem403793 A _8557 P _8558). Qed.
Lemma lem403795 {A : Type'} (s : type1423 A) (P : A -> Prop) (x : A) : term970 A s P x.
Proof. exact (@lem403794 A (term597 A s x) P x). Qed.
Lemma lem403798 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : P x.
Proof. exact (@lem403795 A s P x (@lem403791 A y P s x m h1 h2 h3)). Qed.
Lemma lem403799 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : term971 A P x.
Proof. exact (fun h0 : term554 A P x => @lem403798 A y P s x m h1 h2 h3). Qed.
Lemma lem403801 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403802 {A : Type'} (P : A -> Prop) (x : A) : (term971 A P x) = (P x).
Proof. exact (@lem403801 (P x)). Qed.
Lemma lem403803 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term1218) (h3 : term1296 A y P s x m) : P x.
Proof. exact (EQ_MP (@lem403802 A P x) (@lem403799 A y P s x m h1 h2 h3)). Qed.
Lemma lem403806 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem403808 {A : Type'} (P : A -> Prop) (x : A) : (term554 A P x) = (term972 A P x).
Proof. exact (@lem403806 (P x)). Qed.
Lemma lem403811 {A : Type'} (P : A -> Prop) (x : A) (h1 : term554 A P x) : term972 A P x.
Proof. exact (EQ_MP (@lem403808 A P x) (@lem403223 A P x h1)). Qed.
Lemma lem403814 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (@lem403811 A P x h2 (@lem403803 A y P s x m h1 h3 h4)). Qed.
Lemma lem403815 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : term180.
Proof. exact (fun h0 : ~ False => @lem403814 A y P s x m h1 h2 h3 h4). Qed.
Lemma lem403817 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem403818 : term180 = False.
Proof. exact (@lem403817 False). Qed.
Lemma lem403819 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403818) (@lem403815 A y P s x m h1 h2 h3 h4)). Qed.
Lemma lem403820 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem403819 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem403223 A P x h2)). Qed.
Lemma lem403822 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403820 A y P s x m h1 h2 h3 h4) (@lem403223 A P x h2)). Qed.
Lemma lem403823 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem403822 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem403119 A P x h2)). Qed.
Lemma lem403824 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403823 A y P s x m h1 h2 h3 h4) (@lem403119 A P x h2)). Qed.
Lemma lem403825 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem403824 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402984 A P x h2)). Qed.
Lemma lem403826 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403825 A y P s x m h1 h2 h3 h4) (@lem402984 A P x h2)). Qed.
Lemma lem403827 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem403826 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402984 A P x h2)). Qed.
Lemma lem403828 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403827 A y P s x m h1 h2 h3 h4) (@lem402984 A P x h2)). Qed.
Lemma lem403829 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem403828 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402970 A s h1)). Qed.
Lemma lem403830 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403829 A y P s x m h1 h2 h3 h4) (@lem402970 A s h1)). Qed.
Lemma lem403831 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term1296 A y P s x m) = False.
Proof. exact (prop_ext (fun h5 : term1296 A y P s x m => @lem403830 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402947 A y P s x m h4)). Qed.
Lemma lem403832 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403831 A y P s x m h1 h2 h3 h4) (@lem402947 A y P s x m h4)). Qed.
Lemma lem403833 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h5 : term554 A P x => @lem403832 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402807 A P x h2)). Qed.
Lemma lem403834 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403833 A y P s x m h1 h2 h3 h4) (@lem402807 A P x h2)). Qed.
Lemma lem403835 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : (term608 A s) = False.
Proof. exact (prop_ext (fun h5 : term608 A s => @lem403834 A y P s x m h1 h2 h3 h4) (fun h5 : False => @lem402777 A s h1)). Qed.
Lemma lem403836 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term554 A P x) (h3 : term1218) (h4 : term1296 A y P s x m) : False.
Proof. exact (EQ_MP (@lem403835 A y P s x m h1 h2 h3 h4) (@lem402777 A s h1)). Qed.
Lemma lem403837 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (m : nat -> nat) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1218) (h5 : term1296 A y P s x m) : False.
Proof. exact (ex_elim (@lem402203 A P s x h2) (fun n : nat => fun h0 : term766 A P s x n => @lem403836 A y P s x m h1 h3 h4 h5)). Qed.
Lemma lem403838 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : False.
Proof. exact (ex_elim (@lem402450 A y P s x h4) (fun m : nat -> nat => fun h0 : term1298 A y P s x m => @lem403837 A y P s x m h1 h2 h3 h5 h0)). Qed.
Lemma lem403839 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : (term782 A P s x) = False.
Proof. exact (prop_ext (fun h6 : term782 A P s x => @lem403838 A y P s x h1 h2 h3 h4 h5) (fun h6 : False => @lem402203 A P s x h2)). Qed.
Lemma lem403840 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : False.
Proof. exact (EQ_MP (@lem403839 A y P s x h1 h2 h3 h4 h5) (@lem402203 A P s x h2)). Qed.
Lemma lem403841 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : (term554 A P x) = False.
Proof. exact (prop_ext (fun h6 : term554 A P x => @lem403840 A y P s x h1 h2 h3 h4 h5) (fun h6 : False => @lem402190 A P x h3)). Qed.
Lemma lem403842 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : False.
Proof. exact (EQ_MP (@lem403841 A y P s x h1 h2 h3 h4 h5) (@lem402190 A P x h3)). Qed.
Lemma lem403843 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : (term608 A s) = False.
Proof. exact (prop_ext (fun h6 : term608 A s => @lem403842 A y P s x h1 h2 h3 h4 h5) (fun h6 : False => @lem402164 A s h1)). Qed.
Lemma lem403844 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) (h5 : term1218) : False.
Proof. exact (EQ_MP (@lem403843 A y P s x h1 h2 h3 h4 h5) (@lem402164 A s h1)). Qed.
Lemma lem403845 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) : term1423.
Proof. exact (fun h0 : term1218 => @lem403844 A y P s x h1 h2 h3 h4 h0). Qed.
Lemma lem403846 : term1423 = term1219.
Proof. exact (@lem69 term1218). Qed.
Lemma lem403847 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) (h4 : term1201 A y P s x) : term1219.
Proof. exact (EQ_MP (@lem403846) (@lem403845 A y P s x h1 h2 h3 h4)). Qed.
Lemma lem403848 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term782 A P s x) (h3 : term554 A P x) : term1222 A y P s x.
Proof. exact (fun h0 : term1201 A y P s x => @lem403847 A y P s x h1 h2 h3 h0). Qed.
Lemma lem403849 {A : Type'} (y : A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term554 A P x) : term1224 A y P s x.
Proof. exact (fun h0 : term782 A P s x => @lem403848 A y s P x h1 h0 h2). Qed.
Lemma lem403850 {A : Type'} (y : A) (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : term1226 A y P s x.
Proof. exact (fun h0 : term554 A P x => @lem403849 A y s P x h1 h0). Qed.
Lemma lem403851 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : term1228 A g y P s x.
Proof. exact (fun h0 : term649 A g s => @lem403850 A y P x s h1). Qed.
Lemma lem403852 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1229 A g y P s x.
Proof. exact (fun h0 : term608 A s => @lem403851 A g y P x s h0). Qed.
Lemma lem403857 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1233 A y P s x.
Proof. exact (fun g : A -> A => @lem403852 A g y P s x). Qed.
Lemma lem403862 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term1237 A P s x.
Proof. exact (fun y : A => @lem403857 A y P s x). Qed.
Lemma lem403867 {A : Type'} (s : type1423 A) (x : A) : term1241 A s x.
Proof. exact (fun P : A -> Prop => @lem403862 A P s x). Qed.
Lemma lem403872 {A : Type'} (x : A) : term1245 A x.
Proof. exact (fun s : type1423 A => @lem403867 A s x). Qed.
Lemma lem403877 {A : Type'} : term1249 A.
Proof. exact (fun x : A => @lem403872 A x). Qed.
Lemma lem403878 {A : Type'} : term1248 A.
Proof. exact (EQ_MP (@lem402145 A) (@lem403877 A)). Qed.
Lemma lem403879 {A : Type'} (x : A) : term1424 A x.
Proof. exact (@lem403878 A x). Qed.
Lemma lem403880 {A : Type'} (x : A) : (term1424 A x) = (term1244 A x).
Proof. exact (eq_refl (term1424 A x)). Qed.
Lemma lem403881 {A : Type'} (x : A) : term1244 A x.
Proof. exact (EQ_MP (@lem403880 A x) (@lem403879 A x)). Qed.
Lemma lem403882 {A : Type'} (x : A) (s : type1423 A) : term1425 A x s.
Proof. exact (@lem403881 A x s). Qed.
Lemma lem403883 {A : Type'} (s : type1423 A) (x : A) : (term1425 A x s) = (term1240 A s x).
Proof. exact (eq_refl (term1425 A x s)). Qed.
Lemma lem403884 {A : Type'} (s : type1423 A) (x : A) : term1240 A s x.
Proof. exact (EQ_MP (@lem403883 A s x) (@lem403882 A x s)). Qed.
Lemma lem403885 {A : Type'} (s : type1423 A) (x : A) (P : A -> Prop) : term1426 A s x P.
Proof. exact (@lem403884 A s x P). Qed.
Lemma lem403886 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : (term1426 A s x P) = (term1236 A P s x).
Proof. exact (eq_refl (term1426 A s x P)). Qed.
Lemma lem403887 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) : term1236 A P s x.
Proof. exact (EQ_MP (@lem403886 A P s x) (@lem403885 A s x P)). Qed.
Lemma lem403888 {A : Type'} (P : A -> Prop) (s : type1423 A) (x : A) (y : A) : term1427 A P s x y.
Proof. exact (@lem403887 A P s x y). Qed.
Lemma lem403889 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1427 A P s x y) = (term1232 A y P s x).
Proof. exact (eq_refl (term1427 A P s x y)). Qed.
Lemma lem403890 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1232 A y P s x.
Proof. exact (EQ_MP (@lem403889 A y P s x) (@lem403888 A P s x y)). Qed.
Lemma lem403891 {A : Type'} (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (g : A -> A) : term1428 A y P s x g.
Proof. exact (@lem403890 A y P s x g). Qed.
Lemma lem403892 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : (term1428 A y P s x g) = (term1202 A g y P s x).
Proof. exact (eq_refl (term1428 A y P s x g)). Qed.
Lemma lem403893 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1202 A g y P s x.
Proof. exact (EQ_MP (@lem403892 A g y P s x) (@lem403891 A y P s x g)). Qed.
Lemma lem403895 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) : term1202 A g y P s x.
Proof. exact (@lem401729 A g y P s x (@lem403893 A g y P s x)). Qed.
Lemma lem403896 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (x : A) (s : type1423 A) (h1 : term608 A s) : term1227 A g y P s x.
Proof. exact (@lem403895 A g y P s x (@lem394512 A s h1)). Qed.
Lemma lem403897 {A : Type'} (y : A) (P : A -> Prop) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : term1225 A y P s x.
Proof. exact (@lem403896 A g y P x s h1 (@lem394513 A g s h2)). Qed.
Lemma lem403898 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term1223 A y P s x.
Proof. exact (@lem403897 A y P x g s h1 h2 (@lem394333 A P x h3)). Qed.
Lemma lem403899 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1221 A y P s x.
Proof. exact (@lem403898 A y g s P x h1 h2 h4 (@lem397104 A P s x h3)). Qed.
Lemma lem403900 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1201 A y P s x) : term1206.
Proof. exact (@lem403899 A y g s P x h1 h2 h3 h4 (@lem401713 A y P s x h5)). Qed.
Lemma lem403901 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1201 A y P s x) : False.
Proof. exact (@lem403900 A g y P s x h1 h2 h3 h4 h5 (@lem89997)). Qed.
Lemma lem403902 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1201 A y P s x) : (term1201 A y P s x) = False.
Proof. exact (prop_ext (fun h6 : term1201 A y P s x => @lem403901 A g y P s x h1 h2 h3 h4 h5) (fun h6 : False => @lem401713 A y P s x h5)). Qed.
Lemma lem403903 {A : Type'} (g : A -> A) (y : A) (P : A -> Prop) (s : type1423 A) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) (h5 : term1201 A y P s x) : False.
Proof. exact (EQ_MP (@lem403902 A g y P s x h1 h2 h3 h4 h5) (@lem401713 A y P s x h5)). Qed.
Lemma lem403904 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1200 A y P s x.
Proof. exact (fun h0 : term1201 A y P s x => @lem403903 A g y P s x h1 h2 h3 h4 h0). Qed.
Lemma lem403905 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1199 A y P s x.
Proof. exact (EQ_MP (@lem401712 A y P s x) (@lem403904 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem403906 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term1429 A y P s x.
Proof. exact (conj (@lem401708 A y g s P x h1 h2 h3 h4) (@lem403905 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem403907 {A : Type'} (P : A -> Prop) (s : type1423 A) (y : A) (x : A) : (term1429 A y P s x) = ((term870 A y P s x) = (y = x)).
Proof. exact (@lem32 (term870 A y P s x) (y = x)). Qed.
Lemma lem403908 {A : Type'} (y : A) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : (term870 A y P s x) = (y = x).
Proof. exact (EQ_MP (@lem403907 A P s y x) (@lem403906 A y g s P x h1 h2 h3 h4)). Qed.
Lemma lem403913 {A : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term990 A P s x.
Proof. exact (fun y : A => @lem403908 A y g s P x h1 h2 h3 h4). Qed.
Lemma lem403914 {A : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : term989 A P s x.
Proof. exact (EQ_MP (@lem397954 A P s x) (@lem403913 A g s P x h1 h2 h3 h4)). Qed.
Lemma lem403915 {A : Type'} (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : (term880 A P s x) = x.
Proof. exact (@lem397903 A P s x (@lem403914 A g s P x h1 h2 h3 h4)). Qed.
Lemma lem403917 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) : something_arbitrary = (h x).
Proof. exact (EQ_MP (@lem397141 A B something_arbitrary h x) (@lem397897 A B something_arbitrary h g s P x h1 h2 h3 h4)). Qed.
Lemma lem403918 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) : (term791 A P s x) = (something_arbitrary = (h x)).
Proof. exact (prop_ext (fun h5 : term791 A P s x => @lem403917 A B something_arbitrary h g s P x h1 h2 h3 h4) (fun h5 : something_arbitrary = (h x) => @lem397121 A P s x h3)). Qed.
Lemma lem403919 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term791 A P s x) (h4 : term554 A P x) : something_arbitrary = (h x).
Proof. exact (EQ_MP (@lem403918 A B something_arbitrary h g s P x h1 h2 h3 h4) (@lem397121 A P s x h3)). Qed.
Lemma lem403920 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term889 A B P s something_arbitrary h x.
Proof. exact (fun h0 : term791 A P s x => @lem403919 A B something_arbitrary h g s P x h1 h2 h0 h3). Qed.
Lemma lem403921 {A B : Type'} (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : (term801 A B h P s x) = (h x).
Proof. exact (MK_COMB (@lem397899 A B h) (@lem403915 A g s P x h1 h2 h3 h4)). Qed.
Lemma lem403922 {A B : Type'} (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : (term782 A P s x) = ((term801 A B h P s x) = (h x)).
Proof. exact (prop_ext (fun h5 : term782 A P s x => @lem403921 A B h g s P x h1 h2 h3 h4) (fun h5 : (term801 A B h P s x) = (h x) => @lem397104 A P s x h3)). Qed.
Lemma lem403923 {A B : Type'} (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term782 A P s x) (h4 : term554 A P x) : (term801 A B h P s x) = (h x).
Proof. exact (EQ_MP (@lem403922 A B h g s P x h1 h2 h3 h4) (@lem397104 A P s x h3)). Qed.
Lemma lem403924 {A B : Type'} (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term892 A B P s h x.
Proof. exact (fun h0 : term782 A P s x => @lem403923 A B h g s P x h1 h2 h0 h3). Qed.
Lemma lem403925 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : term895 A B P s something_arbitrary h x.
Proof. exact (conj (@lem403924 A B h g s P x h1 h2 h3) (@lem403920 A B something_arbitrary h g s P x h1 h2 h3)). Qed.
Lemma lem403926 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : (term699 A B h P s x something_arbitrary) = (h x).
Proof. exact (EQ_MP (@lem397103 A B P s something_arbitrary h x) (@lem403925 A B something_arbitrary h g s P x h1 h2 h3)). Qed.
Lemma lem403927 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : term554 A P x) : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x).
Proof. exact (EQ_MP (@lem395012 A B something_arbitrary h g s P x h2 h3) (@lem403926 A B something_arbitrary h g s P x h1 h2 h3)). Qed.
Lemma lem403928 {A B : Type'} (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (P : A -> Prop) (x : A) (h1 : term608 A s) (h2 : term649 A g s) (h3 : P x) : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x).
Proof. exact (EQ_MP (@lem394842 A B something_arbitrary h g s P x h2 h3) (@lem397085 A B h something_arbitrary s P x h1 h3)). Qed.
Lemma lem403929 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x).
Proof. exact (or_elim (@lem394331 A P x) (fun h0 : P x => @lem403928 A B something_arbitrary h g s P x h1 h2 h0) (fun h0 : term554 A P x => @lem403927 A B something_arbitrary h g s P x h1 h2 h0)). Qed.
Lemma lem403930 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : (term649 A g s) = ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)).
Proof. exact (prop_ext (fun h3 : term649 A g s => @lem403929 A B P something_arbitrary h x g s h1 h2) (fun h3 : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x) => @lem394513 A g s h2)). Qed.
Lemma lem403931 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term649 A g s) : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x).
Proof. exact (EQ_MP (@lem403930 A B P something_arbitrary h x g s h1 h2) (@lem394513 A g s h2)). Qed.
Lemma lem403932 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term649 A g s) = ((term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x)).
Proof. exact (prop_ext (fun h3 : term649 A g s => @lem403931 A B P something_arbitrary h x g s h2 h3) (fun h3 : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x) => @lem394652 A g s h1 h2)). Qed.
Lemma lem403933 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (x : A) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term697 A B h P s something_arbitrary x) = (term749 A B P s something_arbitrary g h x).
Proof. exact (EQ_MP (@lem403932 A B P something_arbitrary h x g s h1 h2) (@lem394652 A g s h1 h2)). Qed.
Lemma lem403938 {A B : Type'} (P : A -> Prop) (something_arbitrary : B) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term1430 A B P s something_arbitrary g h.
Proof. exact (fun x : A => @lem403933 A B P something_arbitrary h x g s h1 h2). Qed.
Lemma lem403939 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term646 A B P g h.
Proof. exact (ex_intro (term1431 A B P g h) (term1432 A B h P s) (@lem403938 A B P (@el B) h g s h1 h2)). Qed.
Lemma lem403940 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term641 A g s) : term640 A g s.
Proof. exact (proj2 (@lem394510 A g s h1)). Qed.
Lemma lem403941 {A : Type'} (g : A -> A) (s : type1423 A) (h1 : term641 A g s) : term608 A s.
Proof. exact (proj1 (@lem394510 A g s h1)). Qed.
Lemma lem403942 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term640 A g s) = (term646 A B P g h).
Proof. exact (prop_ext (fun h3 : term640 A g s => @lem403939 A B P h g s h1 h2) (fun h3 : term646 A B P g h => @lem394511 A g s h1)). Qed.
Lemma lem403943 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term646 A B P g h.
Proof. exact (EQ_MP (@lem403942 A B P h g s h1 h2) (@lem394511 A g s h1)). Qed.
Lemma lem403944 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : (term608 A s) = (term646 A B P g h).
Proof. exact (prop_ext (fun h3 : term608 A s => @lem403943 A B P h g s h1 h2) (fun h3 : term646 A B P g h => @lem394512 A s h2)). Qed.
Lemma lem403945 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term640 A g s) (h2 : term608 A s) : term646 A B P g h.
Proof. exact (EQ_MP (@lem403944 A B P h g s h1 h2) (@lem394512 A s h2)). Qed.
Lemma lem403946 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term641 A g s) : (term640 A g s) = (term646 A B P g h).
Proof. exact (prop_ext (fun h3 : term640 A g s => @lem403945 A B P h g s h3 h1) (fun h3 : term646 A B P g h => @lem403940 A g s h2)). Qed.
Lemma lem403947 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term608 A s) (h2 : term641 A g s) : term646 A B P g h.
Proof. exact (EQ_MP (@lem403946 A B P h g s h1 h2) (@lem403940 A g s h2)). Qed.
Lemma lem403948 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term641 A g s) : (term608 A s) = (term646 A B P g h).
Proof. exact (prop_ext (fun h2 : term608 A s => @lem403947 A B P h g s h2 h1) (fun h2 : term646 A B P g h => @lem403941 A g s h1)). Qed.
Lemma lem403949 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (s : type1423 A) (h1 : term641 A g s) : term646 A B P g h.
Proof. exact (EQ_MP (@lem403948 A B P h g s h1) (@lem403941 A g s h1)). Qed.
Lemma lem403950 {A B : Type'} (P : A -> Prop) (h : A -> B) (g : A -> A) (h1 : term643 A g) : term646 A B P g h.
Proof. exact (ex_elim (@lem394509 A g h1) (fun s : type1423 A => fun h0 : term642 A g s => @lem403949 A B P h g s h0)). Qed.
Lemma lem403951 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : term648 A B P g h.
Proof. exact (fun h0 : term643 A g => @lem403950 A B P h g h0). Qed.
Lemma lem403952 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : term647 A B P g h.
Proof. exact (EQ_MP (@lem394508 A B P g h) (@lem403951 A B P g h)). Qed.
Lemma lem403953 {A B : Type'} (P : A -> Prop) (g : A -> A) (h : A -> B) : term646 A B P g h.
Proof. exact (@lem403952 A B P g h (@lem394350 A g)). Qed.
Lemma lem403958 {A B : Type'} (P : A -> Prop) (g : A -> A) : term1433 A B P g.
Proof. exact (fun h : A -> B => @lem403953 A B P g h). Qed.
Lemma lem403963 {A B : Type'} (P : A -> Prop) : term1434 A B P.
Proof. exact (fun g : A -> A => @lem403958 A B P g). Qed.
Lemma lem403968 {A B : Type'} : term1435 A B.
Proof. exact (fun P : A -> Prop => @lem403963 A B P). Qed.
