Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_LE_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVIDES_LE_spec.
Require Import LE_REFL_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem3086887 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3086888 : term1 = term2.
Proof. exact (@lem3086887 term1). Qed.
Lemma lem3086889 : term2 = term1.
Proof. exact (SYM (@lem3086888)). Qed.
Lemma lem3086890 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem3086893 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem3086894 : term5.
Proof. exact (fun h0 : term4 => @lem3086893 h0). Qed.
Lemma lem3086895 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem3086896 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem3086897 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem3086895 h2 (@lem3086896 h1)). Qed.
Lemma lem3086898 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem3086897 h1 h0). Qed.
Lemma lem3086899 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem3086900 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem3086898 h1 (@lem3086899 h2)). Qed.
Lemma lem3086901 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem3086900 h0 h1). Qed.
Lemma lem3086902 : term7.
Proof. exact (fun h0 : term5 => @lem3086901 h0). Qed.
Lemma lem3086905 : term5.
Proof. exact (@lem3086902 (@lem3086894)). Qed.
Lemma lem3086929 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3086930 : term8 = term9.
Proof. exact (@lem3086929 term10). Qed.
Lemma lem3086943 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem3086944 : term12 = term13.
Proof. exact (MK_COMB (@lem3086943) (@lem3086930)). Qed.
Lemma lem3086947 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem3086954 : term4 = term15.
Proof. exact (MK_COMB (@lem3086947) (@lem3086944)). Qed.
Lemma lem3086963 (m : nat) (n : nat) : (term16 m n) = (term16 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem3086964 (m : nat) : (term17 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem3086963 m n)). Qed.
Lemma lem3086965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086966 (m : nat) : (term18 m) = (term18 m).
Proof. exact (MK_COMB (@lem3086965) (@lem3086964 m)). Qed.
Lemma lem3086967 : term19 = term19.
Proof. exact (fun_ext (fun m : nat => @lem3086966 m)). Qed.
Lemma lem3086968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086969 : term10 = term10.
Proof. exact (MK_COMB (@lem3086968) (@lem3086967)). Qed.
Lemma lem3086970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3086971 : term9 = term9.
Proof. exact (MK_COMB (@lem3086970) (@lem3086969)). Qed.
Lemma lem3086972 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem3086973 : term20 = term20.
Proof. exact (fun_ext (fun n : nat => @lem3086972 n)). Qed.
Lemma lem3086974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086975 : term21 = term21.
Proof. exact (MK_COMB (@lem3086974) (@lem3086973)). Qed.
Lemma lem3086976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3086977 : term11 = term11.
Proof. exact (MK_COMB (@lem3086976) (@lem3086975)). Qed.
Lemma lem3086978 : term13 = term13.
Proof. exact (MK_COMB (@lem3086977) (@lem3086971)). Qed.
Lemma lem3086991 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem3086992 (m : nat) : (term23 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem3086991 m n)). Qed.
Lemma lem3086993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086994 (m : nat) : (term24 m) = (term24 m).
Proof. exact (MK_COMB (@lem3086993) (@lem3086992 m)). Qed.
Lemma lem3086995 : term25 = term25.
Proof. exact (fun_ext (fun m : nat => @lem3086994 m)). Qed.
Lemma lem3086996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3086997 : term1 = term1.
Proof. exact (MK_COMB (@lem3086996) (@lem3086995)). Qed.
Lemma lem3086998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3086999 : term3 = term3.
Proof. exact (MK_COMB (@lem3086998) (@lem3086997)). Qed.
Lemma lem3087000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3087001 : term14 = term14.
Proof. exact (MK_COMB (@lem3087000) (@lem3086999)). Qed.
Lemma lem3087002 : term15 = term15.
Proof. exact (MK_COMB (@lem3087001) (@lem3086978)). Qed.
Lemma lem3087049 : term4 = term15.
Proof. exact (TRANS (@lem3086954) (@lem3087002)). Qed.
Lemma lem3087050 : term15 = term4.
Proof. exact (SYM (@lem3087049)). Qed.
Lemma lem3087051 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem3087052 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem3087053 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem3087061 (n : nat) (m : nat) : (term26 n m) = (term27 n m).
Proof. exact (@lem17265 (n = (NUMERAL 0)) (m = (NUMERAL 0))). Qed.
Lemma lem3087063 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem3087064 (n : nat) (m : nat) : (term29 n m) = (term30 n m).
Proof. exact (MK_COMB (@lem3087063 m n) (@lem3087061 n m)). Qed.
Lemma lem3087065 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem3087066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3087067 (n : nat) (m : nat) : (term32 n m) = (term33 n m).
Proof. exact (MK_COMB (@lem3087066) (@lem3087064 n m)). Qed.
Lemma lem3087068 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem3087067 n m) (@lem3087065 m n)). Qed.
Lemma lem3087069 (m : nat) (n : nat) : (term36 m n) = (term34 m n).
Proof. exact (@lem17362 (term29 n m) (Peano.le m n)). Qed.
Lemma lem3087070 (m : nat) (n : nat) : (term36 m n) = (term35 m n).
Proof. exact (TRANS (@lem3087069 m n) (@lem3087068 m n)). Qed.
Lemma lem3087071 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3087072 (m : nat) : (term39 m) = (term40 m).
Proof. exact (@lem3087071 (term23 m)). Qed.
Lemma lem3087073 (m : nat) (n : nat) : (term41 m n) = (term22 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem3087074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3087075 (m : nat) (n : nat) : (term42 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem3087074) (@lem3087073 m n)). Qed.
Lemma lem3087076 (m : nat) (n : nat) : (term42 m n) = (term35 m n).
Proof. exact (TRANS (@lem3087075 m n) (@lem3087070 m n)). Qed.
Lemma lem3087077 (m : nat) : (term43 m) = (term44 m).
Proof. exact (fun_ext (fun n : nat => @lem3087076 m n)). Qed.
Lemma lem3087078 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3087079 (m : nat) : (term40 m) = (term45 m).
Proof. exact (MK_COMB (@lem3087078) (@lem3087077 m)). Qed.
Lemma lem3087080 (m : nat) : (term39 m) = (term45 m).
Proof. exact (TRANS (@lem3087072 m) (@lem3087079 m)). Qed.
Lemma lem3087081 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3087082 : term3 = term46.
Proof. exact (@lem3087081 term25). Qed.
Lemma lem3087083 (m : nat) : (term47 m) = (term24 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem3087084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3087085 (m : nat) : (term48 m) = (term39 m).
Proof. exact (MK_COMB (@lem3087084) (@lem3087083 m)). Qed.
Lemma lem3087086 (m : nat) : (term48 m) = (term45 m).
Proof. exact (TRANS (@lem3087085 m) (@lem3087080 m)). Qed.
Lemma lem3087087 : term49 = term50.
Proof. exact (fun_ext (fun m : nat => @lem3087086 m)). Qed.
Lemma lem3087088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3087089 : term46 = term51.
Proof. exact (MK_COMB (@lem3087088) (@lem3087087)). Qed.
Lemma lem3087146 : term3 = term51.
Proof. exact (TRANS (@lem3087082) (@lem3087089)). Qed.
Lemma lem3087147 (h1 : term3) : term51.
Proof. exact (EQ_MP (@lem3087146) (@lem3087051 h1)). Qed.
Lemma lem3087148 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem3087149 : term20 = term20.
Proof. exact (fun_ext (fun n : nat => @lem3087148 n)). Qed.
Lemma lem3087150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087159 : term21 = term21.
Proof. exact (MK_COMB (@lem3087150) (@lem3087149)). Qed.
Lemma lem3087160 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem3087159) (@lem3087052 h1)). Qed.
Lemma lem3087171 (m : nat) (n : nat) : (term16 m n) = (term52 m n).
Proof. exact (@lem17265 (num_divides m n) (term53 m n)). Qed.
Lemma lem3087172 (m : nat) : (term17 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem3087171 m n)). Qed.
Lemma lem3087173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087174 (m : nat) : (term18 m) = (term55 m).
Proof. exact (MK_COMB (@lem3087173) (@lem3087172 m)). Qed.
Lemma lem3087175 : term19 = term56.
Proof. exact (fun_ext (fun m : nat => @lem3087174 m)). Qed.
Lemma lem3087176 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087233 : term10 = term57.
Proof. exact (MK_COMB (@lem3087176) (@lem3087175)). Qed.
Lemma lem3087234 (h1 : term10) : term57.
Proof. exact (EQ_MP (@lem3087233) (@lem3087053 h1)). Qed.
Lemma lem3087235 (m : nat) (h1 : term45 m) : term45 m.
Proof. exact (h1). Qed.
Lemma lem3087241 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem3087242 : term20 = term20.
Proof. exact (fun_ext (fun n : nat => @lem3087241 n)). Qed.
Lemma lem3087243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087244 : term21 = term21.
Proof. exact (MK_COMB (@lem3087243) (@lem3087242)). Qed.
Lemma lem3087245 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem3087244) (@lem3087160 h1)). Qed.
Lemma lem3087270 (m : nat) (n : nat) : (term52 m n) = (term52 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem3087271 (m : nat) : (term54 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem3087270 m n)). Qed.
Lemma lem3087272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087273 (m : nat) : (term55 m) = (term55 m).
Proof. exact (MK_COMB (@lem3087272) (@lem3087271 m)). Qed.
Lemma lem3087274 : term56 = term56.
Proof. exact (fun_ext (fun m : nat => @lem3087273 m)). Qed.
Lemma lem3087275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087276 : term57 = term57.
Proof. exact (MK_COMB (@lem3087275) (@lem3087274)). Qed.
Lemma lem3087277 (h1 : term10) : term57.
Proof. exact (EQ_MP (@lem3087276) (@lem3087234 h1)). Qed.
Lemma lem3087315 (m : nat) (n : nat) (h1 : term35 m n) : term35 m n.
Proof. exact (h1). Qed.
Lemma lem3087317 (m : nat) (n : nat) (h1 : term35 m n) : term30 n m.
Proof. exact (proj1 (@lem3087315 m n h1)). Qed.
Lemma lem3087318 (m : nat) (n : nat) (h1 : term35 m n) : term27 n m.
Proof. exact (proj2 (@lem3087317 m n h1)). Qed.
Lemma lem3087342 (m : nat) (n : nat) : (term52 m n) = (term52 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem3087343 (m : nat) : (term54 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem3087342 m n)). Qed.
Lemma lem3087344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087345 (m : nat) : (term55 m) = (term55 m).
Proof. exact (MK_COMB (@lem3087344) (@lem3087343 m)). Qed.
Lemma lem3087346 : term56 = term56.
Proof. exact (fun_ext (fun m : nat => @lem3087345 m)). Qed.
Lemma lem3087347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087349 : term57 = term57.
Proof. exact (MK_COMB (@lem3087347) (@lem3087346)). Qed.
Lemma lem3087350 (h1 : term10) : term57.
Proof. exact (EQ_MP (@lem3087349) (@lem3087277 h1)). Qed.
Lemma lem3087362 (n : nat) (h1 : term58 n) : term58 n.
Proof. exact (h1). Qed.
Lemma lem3087364 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem3087365 : term20 = term20.
Proof. exact (fun_ext (fun n : nat => @lem3087364 n)). Qed.
Lemma lem3087366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087368 : term21 = term21.
Proof. exact (MK_COMB (@lem3087366) (@lem3087365)). Qed.
Lemma lem3087369 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem3087368) (@lem3087245 h1)). Qed.
Lemma lem3087383 (m : nat) (n : nat) : (term52 m n) = (term52 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem3087384 (m : nat) : (term54 m) = (term54 m).
Proof. exact (fun_ext (fun n : nat => @lem3087383 m n)). Qed.
Lemma lem3087385 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087386 (m : nat) : (term55 m) = (term55 m).
Proof. exact (MK_COMB (@lem3087385) (@lem3087384 m)). Qed.
Lemma lem3087387 : term56 = term56.
Proof. exact (fun_ext (fun m : nat => @lem3087386 m)). Qed.
Lemma lem3087388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3087390 : term57 = term57.
Proof. exact (MK_COMB (@lem3087388) (@lem3087387)). Qed.
Lemma lem3087391 (h1 : term10) : term57.
Proof. exact (EQ_MP (@lem3087390) (@lem3087277 h1)). Qed.
Lemma lem3087403 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3087407 (_32110 : nat) (h1 : term10) : term59 _32110.
Proof. exact (@lem3087350 h1 _32110). Qed.
Lemma lem3087408 (_32110 : nat) : (term59 _32110) = (term55 _32110).
Proof. exact (eq_refl (term59 _32110)). Qed.
Lemma lem3087409 (_32110 : nat) (h1 : term10) : term55 _32110.
Proof. exact (EQ_MP (@lem3087408 _32110) (@lem3087407 _32110 h1)). Qed.
Lemma lem3087410 (_32110 : nat) (_32111 : nat) (h1 : term10) : term60 _32110 _32111.
Proof. exact (@lem3087409 _32110 h1 _32111). Qed.
Lemma lem3087411 (_32110 : nat) (_32111 : nat) : (term60 _32110 _32111) = (term52 _32110 _32111).
Proof. exact (eq_refl (term60 _32110 _32111)). Qed.
Lemma lem3087413 (_32112 : nat) (h1 : term21) : term61 _32112.
Proof. exact (@lem3087369 h1 _32112). Qed.
Lemma lem3087414 (_32112 : nat) : (term61 _32112) = (Peano.le _32112 _32112).
Proof. exact (eq_refl (term61 _32112)). Qed.
Lemma lem3087416 (_32113 : nat) (h1 : term10) : term59 _32113.
Proof. exact (@lem3087391 h1 _32113). Qed.
Lemma lem3087417 (_32113 : nat) : (term59 _32113) = (term55 _32113).
Proof. exact (eq_refl (term59 _32113)). Qed.
Lemma lem3087418 (_32113 : nat) (h1 : term10) : term55 _32113.
Proof. exact (EQ_MP (@lem3087417 _32113) (@lem3087416 _32113 h1)). Qed.
Lemma lem3087419 (_32113 : nat) (_32114 : nat) (h1 : term10) : term60 _32113 _32114.
Proof. exact (@lem3087418 _32113 h1 _32114). Qed.
Lemma lem3087420 (_32113 : nat) (_32114 : nat) : (term60 _32113 _32114) = (term52 _32113 _32114).
Proof. exact (eq_refl (term60 _32113 _32114)). Qed.
Lemma lem3087433 (_32110 : nat) (_32111 : nat) (h1 : term10) : term52 _32110 _32111.
Proof. exact (EQ_MP (@lem3087411 _32110 _32111) (@lem3087410 _32110 _32111 h1)). Qed.
Lemma lem3087439 (n : nat) (h1 : term58 n) : term58 n.
Proof. exact (h1). Qed.
Lemma lem3087453 (m : nat) (n : nat) (h1 : term35 m n) : term31 m n.
Proof. exact (proj2 (@lem3087315 m n h1)). Qed.
Lemma lem3087455 (m : nat) (n : nat) (h1 : term35 m n) : num_divides m n.
Proof. exact (proj1 (@lem3087317 m n h1)). Qed.
Lemma lem3087457 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3087499 (_32113 : nat) (_32114 : nat) (h1 : term10) : term52 _32113 _32114.
Proof. exact (EQ_MP (@lem3087420 _32113 _32114) (@lem3087419 _32113 _32114 h1)). Qed.
Lemma lem3087500 (n : nat) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem3087501 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term63 n m) = (term64 n).
Proof. exact (MK_COMB (@lem3087500 n) (@lem3087457 m h1)). Qed.
Lemma lem3087502 (n : nat) : (term64 n) = (term65 n).
Proof. exact (eq_refl (term64 n)). Qed.
Lemma lem3087503 (n : nat) (m : nat) : (term66 n m) = (term66 n m).
Proof. exact (eq_refl (term66 n m)). Qed.
Lemma lem3087504 (m : nat) (n : nat) : ((term63 n m) = (term64 n)) = ((term63 n m) = (term65 n)).
Proof. exact (MK_COMB (@lem3087503 n m) (@lem3087502 n)). Qed.
Lemma lem3087505 (m : nat) (n : nat) : (term63 n m) = (term31 m n).
Proof. exact (eq_refl (term63 n m)). Qed.
Lemma lem3087506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3087507 (m : nat) (n : nat) : (term66 n m) = (term67 m n).
Proof. exact (MK_COMB (@lem3087506) (@lem3087505 m n)). Qed.
Lemma lem3087508 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem3087509 (m : nat) (n : nat) : ((term63 n m) = (term65 n)) = ((term31 m n) = (term65 n)).
Proof. exact (MK_COMB (@lem3087507 m n) (@lem3087508 n)). Qed.
Lemma lem3087510 (m : nat) (n : nat) : ((term63 n m) = (term64 n)) = ((term31 m n) = (term65 n)).
Proof. exact (TRANS (@lem3087504 m n) (@lem3087509 m n)). Qed.
Lemma lem3087511 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term31 m n) = (term65 n).
Proof. exact (EQ_MP (@lem3087510 m n) (@lem3087501 n m h1)). Qed.
Lemma lem3087512 (n : nat) (m : nat) (h1 : term35 m n) (h2 : m = (NUMERAL 0)) : term65 n.
Proof. exact (EQ_MP (@lem3087511 n m h2) (@lem3087453 m n h1)). Qed.
Lemma lem3087513 (n : nat) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem3087514 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term69 n m) = (term70 n).
Proof. exact (MK_COMB (@lem3087513 n) (@lem3087457 m h1)). Qed.
Lemma lem3087515 (n : nat) : (term70 n) = (term71 n).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem3087516 (n : nat) (m : nat) : (term72 n m) = (term72 n m).
Proof. exact (eq_refl (term72 n m)). Qed.
Lemma lem3087517 (m : nat) (n : nat) : ((term69 n m) = (term70 n)) = ((term69 n m) = (term71 n)).
Proof. exact (MK_COMB (@lem3087516 n m) (@lem3087515 n)). Qed.
Lemma lem3087518 (m : nat) (n : nat) : (term69 n m) = (num_divides m n).
Proof. exact (eq_refl (term69 n m)). Qed.
Lemma lem3087519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3087520 (m : nat) (n : nat) : (term72 n m) = (term73 m n).
Proof. exact (MK_COMB (@lem3087519) (@lem3087518 m n)). Qed.
Lemma lem3087521 (n : nat) : (term71 n) = (term71 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem3087522 (m : nat) (n : nat) : ((term69 n m) = (term71 n)) = ((num_divides m n) = (term71 n)).
Proof. exact (MK_COMB (@lem3087520 m n) (@lem3087521 n)). Qed.
Lemma lem3087523 (m : nat) (n : nat) : ((term69 n m) = (term70 n)) = ((num_divides m n) = (term71 n)).
Proof. exact (TRANS (@lem3087517 m n) (@lem3087522 m n)). Qed.
Lemma lem3087524 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (num_divides m n) = (term71 n).
Proof. exact (EQ_MP (@lem3087523 m n) (@lem3087514 n m h1)). Qed.
Lemma lem3087575 (m : nat) (n : nat) (h1 : term35 m n) : num_divides m n.
Proof. exact (proj1 (@lem3087317 m n h1)). Qed.
Lemma lem3087576 (m : nat) (n : nat) (h1 : term35 m n) : term74 m n.
Proof. exact (fun h0 : term75 m n => @lem3087575 m n h1). Qed.
Lemma lem3087578 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087579 (m : nat) (n : nat) : (term74 m n) = (num_divides m n).
Proof. exact (@lem3087578 (num_divides m n)). Qed.
Lemma lem3087580 (m : nat) (n : nat) (h1 : term35 m n) : num_divides m n.
Proof. exact (EQ_MP (@lem3087579 m n) (@lem3087576 m n h1)). Qed.
Lemma lem3087582 (m : nat) (n : nat) (h1 : term35 m n) : term31 m n.
Proof. exact (proj2 (@lem3087315 m n h1)). Qed.
Lemma lem3087583 (m : nat) (n : nat) (h1 : term35 m n) : term77 m n.
Proof. exact (fun h0 : Peano.le m n => @lem3087582 m n h1). Qed.
Lemma lem3087585 (p : Prop) : (term78 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3087586 (m : nat) (n : nat) : (term77 m n) = (term31 m n).
Proof. exact (@lem3087585 (Peano.le m n)). Qed.
Lemma lem3087587 (m : nat) (n : nat) (h1 : term35 m n) : term31 m n.
Proof. exact (EQ_MP (@lem3087586 m n) (@lem3087583 m n h1)). Qed.
Lemma lem3087593 (q : Prop) (p : Prop) (r : Prop) : (term79 p q r) = (term79 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3087594 (_32110 : nat) (_32111 : nat) : (term52 _32110 _32111) = (term80 _32110 _32111).
Proof. exact (@lem3087593 (Peano.le _32110 _32111) (term75 _32110 _32111) (_32111 = (NUMERAL 0))). Qed.
Lemma lem3087608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3087609 (_32110 : nat) (_32111 : nat) : (term81 _32110 _32111) = (term82 _32110 _32111).
Proof. exact (@lem3087608 (_32111 = (NUMERAL 0)) (term75 _32110 _32111)). Qed.
Lemma lem3087617 (_32110 : nat) (_32111 : nat) : (term83 _32110 _32111) = (term83 _32110 _32111).
Proof. exact (eq_refl (term83 _32110 _32111)). Qed.
Lemma lem3087618 (_32110 : nat) (_32111 : nat) : (term80 _32110 _32111) = (term84 _32110 _32111).
Proof. exact (MK_COMB (@lem3087617 _32110 _32111) (@lem3087609 _32110 _32111)). Qed.
Lemma lem3087629 (_32110 : nat) (_32111 : nat) : (term52 _32110 _32111) = (term84 _32110 _32111).
Proof. exact (TRANS (@lem3087594 _32110 _32111) (@lem3087618 _32110 _32111)). Qed.
Lemma lem3087630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3087631 (_32110 : nat) (_32111 : nat) : (term85 _32110 _32111) = (term86 _32110 _32111).
Proof. exact (MK_COMB (@lem3087630) (@lem3087629 _32110 _32111)). Qed.
Lemma lem3087647 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3087648 (_32110 : nat) (_32111 : nat) : (term87 _32110 _32111) = (term88 _32110 _32111).
Proof. exact (@lem3087647 (Peano.le _32110 _32111) (term75 _32110 _32111)). Qed.
Lemma lem3087654 (_32111 : nat) : (term89 _32111) = (term89 _32111).
Proof. exact (eq_refl (term89 _32111)). Qed.
Lemma lem3087655 (_32110 : nat) (_32111 : nat) : (term90 _32110 _32111) = (term91 _32110 _32111).
Proof. exact (MK_COMB (@lem3087654 _32111) (@lem3087648 _32110 _32111)). Qed.
Lemma lem3087659 (q : Prop) (p : Prop) (r : Prop) : (term79 p q r) = (term79 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3087660 (_32110 : nat) (_32111 : nat) : (term91 _32110 _32111) = (term84 _32110 _32111).
Proof. exact (@lem3087659 (Peano.le _32110 _32111) (_32111 = (NUMERAL 0)) (term75 _32110 _32111)). Qed.
Lemma lem3087678 (_32110 : nat) (_32111 : nat) : (term90 _32110 _32111) = (term84 _32110 _32111).
Proof. exact (TRANS (@lem3087655 _32110 _32111) (@lem3087660 _32110 _32111)). Qed.
Lemma lem3087679 (_32110 : nat) (_32111 : nat) : ((term52 _32110 _32111) = (term90 _32110 _32111)) = ((term84 _32110 _32111) = (term84 _32110 _32111)).
Proof. exact (MK_COMB (@lem3087631 _32110 _32111) (@lem3087678 _32110 _32111)). Qed.
Lemma lem3087681 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3087682 (x : Prop) : (x = x) = True.
Proof. exact (@lem3087681 Prop x). Qed.
Lemma lem3087683 (_32110 : nat) (_32111 : nat) : ((term84 _32110 _32111) = (term84 _32110 _32111)) = True.
Proof. exact (@lem3087682 (term84 _32110 _32111)). Qed.
Lemma lem3087684 (_32110 : nat) (_32111 : nat) : ((term52 _32110 _32111) = (term90 _32110 _32111)) = True.
Proof. exact (TRANS (@lem3087679 _32110 _32111) (@lem3087683 _32110 _32111)). Qed.
Lemma lem3087685 (_32110 : nat) (_32111 : nat) : True = ((term52 _32110 _32111) = (term90 _32110 _32111)).
Proof. exact (SYM (@lem3087684 _32110 _32111)). Qed.
Lemma lem3087686 (_32110 : nat) (_32111 : nat) : (term52 _32110 _32111) = (term90 _32110 _32111).
Proof. exact (EQ_MP (@lem3087685 _32110 _32111) (@lem0)). Qed.
Lemma lem3087687 (_32110 : nat) (_32111 : nat) (h1 : term10) : term90 _32110 _32111.
Proof. exact (EQ_MP (@lem3087686 _32110 _32111) (@lem3087433 _32110 _32111 h1)). Qed.
Lemma lem3087689 (b : Prop) (a : Prop) : (a \/ b) = (term92 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3087690 (_32110 : nat) (_32111 : nat) : (term90 _32110 _32111) = (term93 _32110 _32111).
Proof. exact (@lem3087689 (term87 _32110 _32111) (_32111 = (NUMERAL 0))). Qed.
Lemma lem3087692 (a : Prop) (b : Prop) : (term94 a b) = (term95 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3087693 (_32110 : nat) (_32111 : nat) : (term96 _32110 _32111) = (term97 _32110 _32111).
Proof. exact (@lem3087692 (term75 _32110 _32111) (Peano.le _32110 _32111)). Qed.
Lemma lem3087695 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3087696 (_32110 : nat) (_32111 : nat) : (term99 _32110 _32111) = (num_divides _32110 _32111).
Proof. exact (@lem3087695 (num_divides _32110 _32111)). Qed.
Lemma lem3087697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3087698 (_32110 : nat) (_32111 : nat) : (term100 _32110 _32111) = (term28 _32110 _32111).
Proof. exact (MK_COMB (@lem3087697) (@lem3087696 _32110 _32111)). Qed.
Lemma lem3087699 (_32110 : nat) (_32111 : nat) : (term31 _32110 _32111) = (term31 _32110 _32111).
Proof. exact (eq_refl (term31 _32110 _32111)). Qed.
Lemma lem3087700 (_32110 : nat) (_32111 : nat) : (term97 _32110 _32111) = (term101 _32110 _32111).
Proof. exact (MK_COMB (@lem3087698 _32110 _32111) (@lem3087699 _32110 _32111)). Qed.
Lemma lem3087701 (_32110 : nat) (_32111 : nat) : (term96 _32110 _32111) = (term101 _32110 _32111).
Proof. exact (TRANS (@lem3087693 _32110 _32111) (@lem3087700 _32110 _32111)). Qed.
Lemma lem3087702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3087703 (_32110 : nat) (_32111 : nat) : (term102 _32110 _32111) = (term103 _32110 _32111).
Proof. exact (MK_COMB (@lem3087702) (@lem3087701 _32110 _32111)). Qed.
Lemma lem3087704 (_32111 : nat) : (_32111 = (NUMERAL 0)) = (_32111 = (NUMERAL 0)).
Proof. exact (eq_refl (_32111 = (NUMERAL 0))). Qed.
Lemma lem3087705 (_32110 : nat) (_32111 : nat) : (term93 _32110 _32111) = (term104 _32110 _32111).
Proof. exact (MK_COMB (@lem3087703 _32110 _32111) (@lem3087704 _32111)). Qed.
Lemma lem3087706 (_32110 : nat) (_32111 : nat) : (term90 _32110 _32111) = (term104 _32110 _32111).
Proof. exact (TRANS (@lem3087690 _32110 _32111) (@lem3087705 _32110 _32111)). Qed.
Lemma lem3087708 (m : nat) (n : nat) (h1 : term35 m n) : term101 m n.
Proof. exact (conj (@lem3087580 m n h1) (@lem3087587 m n h1)). Qed.
Lemma lem3087710 (_32110 : nat) (_32111 : nat) (h1 : term10) : term104 _32110 _32111.
Proof. exact (EQ_MP (@lem3087706 _32110 _32111) (@lem3087687 _32110 _32111 h1)). Qed.
Lemma lem3087711 (m : nat) (n : nat) (h1 : term10) : term104 m n.
Proof. exact (@lem3087710 m n h1). Qed.
Lemma lem3087714 (m : nat) (n : nat) (h1 : term10) (h2 : term35 m n) : n = (NUMERAL 0).
Proof. exact (@lem3087711 m n h1 (@lem3087708 m n h2)). Qed.
Lemma lem3087715 (m : nat) (n : nat) (h1 : term10) (h2 : term35 m n) : term105 n.
Proof. exact (fun h0 : term58 n => @lem3087714 m n h1 h2). Qed.
Lemma lem3087717 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087718 (n : nat) : (term105 n) = (n = (NUMERAL 0)).
Proof. exact (@lem3087717 (n = (NUMERAL 0))). Qed.
Lemma lem3087719 (m : nat) (n : nat) (h1 : term10) (h2 : term35 m n) : n = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3087718 n) (@lem3087715 m n h1 h2)). Qed.
Lemma lem3087722 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3087724 (n : nat) : (term58 n) = (term106 n).
Proof. exact (@lem3087722 (n = (NUMERAL 0))). Qed.
Lemma lem3087727 (n : nat) (h1 : term58 n) : term106 n.
Proof. exact (EQ_MP (@lem3087724 n) (@lem3087439 n h1)). Qed.
Lemma lem3087730 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : False.
Proof. exact (@lem3087727 n h2 (@lem3087719 m n h1 h3)). Qed.
Lemma lem3087731 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : term107.
Proof. exact (fun h0 : ~ False => @lem3087730 m n h1 h2 h3). Qed.
Lemma lem3087733 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087734 : term107 = False.
Proof. exact (@lem3087733 False). Qed.
Lemma lem3087735 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3087734) (@lem3087731 m n h1 h2 h3)). Qed.
Lemma lem3087755 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3087756 (_32139 : nat) (_32141 : nat) (h1 : _32139 = _32141) : _32139 = _32141.
Proof. exact (h1). Qed.
Lemma lem3087757 (_32140 : nat) (_32142 : nat) (h1 : _32140 = _32142) : _32140 = _32142.
Proof. exact (h1). Qed.
Lemma lem3087758 (_32139 : nat) (_32141 : nat) (h1 : _32139 = _32141) : (Peano.le _32139) = (Peano.le _32141).
Proof. exact (MK_COMB (@lem3087755) (@lem3087756 _32139 _32141 h1)). Qed.
Lemma lem3087759 (_32139 : nat) (_32141 : nat) (_32140 : nat) (_32142 : nat) (h1 : _32139 = _32141) (h2 : _32140 = _32142) : (Peano.le _32139 _32140) = (Peano.le _32141 _32142).
Proof. exact (MK_COMB (@lem3087758 _32139 _32141 h1) (@lem3087757 _32140 _32142 h2)). Qed.
Lemma lem3087761 (b : Prop) (a : Prop) : term108 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3087762 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : term109 _32141 _32142 _32139 _32140.
Proof. exact (@lem3087761 (Peano.le _32141 _32142) (Peano.le _32139 _32140)). Qed.
Lemma lem3087763 (_32139 : nat) (_32141 : nat) (_32140 : nat) (_32142 : nat) (h1 : _32139 = _32141) (h2 : _32140 = _32142) : term110 _32141 _32142 _32139 _32140.
Proof. exact (@lem3087762 _32141 _32142 _32139 _32140 (@lem3087759 _32139 _32141 _32140 _32142 h1 h2)). Qed.
Lemma lem3087764 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) (h1 : _32139 = _32141) : term111 _32141 _32142 _32139 _32140.
Proof. exact (fun h0 : _32140 = _32142 => @lem3087763 _32139 _32141 _32140 _32142 h1 h0). Qed.
Lemma lem3087766 (a : Prop) (b : Prop) : (a -> b) = (term112 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3087767 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term111 _32141 _32142 _32139 _32140) = (term113 _32141 _32142 _32139 _32140).
Proof. exact (@lem3087766 (_32140 = _32142) (term110 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087768 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) (h1 : _32139 = _32141) : term113 _32141 _32142 _32139 _32140.
Proof. exact (EQ_MP (@lem3087767 _32141 _32142 _32139 _32140) (@lem3087764 _32142 _32140 _32139 _32141 h1)). Qed.
Lemma lem3087769 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : term114 _32141 _32142 _32139 _32140.
Proof. exact (fun h0 : _32139 = _32141 => @lem3087768 _32142 _32140 _32139 _32141 h0). Qed.
Lemma lem3087771 (a : Prop) (b : Prop) : (a -> b) = (term112 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3087772 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term114 _32141 _32142 _32139 _32140) = (term115 _32141 _32142 _32139 _32140).
Proof. exact (@lem3087771 (_32139 = _32141) (term113 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087773 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : term115 _32141 _32142 _32139 _32140.
Proof. exact (EQ_MP (@lem3087772 _32141 _32142 _32139 _32140) (@lem3087769 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087785 (n : nat) (m : nat) (h1 : term35 m n) (h2 : m = (NUMERAL 0)) : term71 n.
Proof. exact (EQ_MP (@lem3087524 n m h2) (@lem3087455 m n h1)). Qed.
Lemma lem3087786 (n : nat) (m : nat) (h1 : term35 m n) (h2 : m = (NUMERAL 0)) : term116 n.
Proof. exact (fun h0 : term117 n => @lem3087785 n m h1 h2). Qed.
Lemma lem3087788 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087789 (n : nat) : (term116 n) = (term71 n).
Proof. exact (@lem3087788 (term71 n)). Qed.
Lemma lem3087790 (n : nat) (m : nat) (h1 : term35 m n) (h2 : m = (NUMERAL 0)) : term71 n.
Proof. exact (EQ_MP (@lem3087789 n) (@lem3087786 n m h1 h2)). Qed.
Lemma lem3087792 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3087793 (n : nat) : n = n.
Proof. exact (@lem3087792 n). Qed.
Lemma lem3087794 (n : nat) : term118 n.
Proof. exact (fun h0 : term119 n => @lem3087793 n). Qed.
Lemma lem3087796 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087797 (n : nat) : (term118 n) = (n = n).
Proof. exact (@lem3087796 (n = n)). Qed.
Lemma lem3087798 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem3087797 n) (@lem3087794 n)). Qed.
Lemma lem3087801 (n : nat) (h1 : term65 n) : term65 n.
Proof. exact (h1). Qed.
Lemma lem3087802 (n : nat) (h1 : term65 n) : term120 n.
Proof. exact (fun h0 : term121 n => @lem3087801 n h1). Qed.
Lemma lem3087804 (p : Prop) : (term78 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3087805 (n : nat) : (term120 n) = (term65 n).
Proof. exact (@lem3087804 (term121 n)). Qed.
Lemma lem3087806 (n : nat) (h1 : term65 n) : term65 n.
Proof. exact (EQ_MP (@lem3087805 n) (@lem3087802 n h1)). Qed.
Lemma lem3087808 (_32112 : nat) (h1 : term21) : Peano.le _32112 _32112.
Proof. exact (EQ_MP (@lem3087414 _32112) (@lem3087413 _32112 h1)). Qed.
Lemma lem3087809 (n : nat) (h1 : term21) : Peano.le n n.
Proof. exact (@lem3087808 n h1). Qed.
Lemma lem3087810 (n : nat) (h1 : term21) : term122 n.
Proof. exact (fun h0 : term123 n => @lem3087809 n h1). Qed.
Lemma lem3087812 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087813 (n : nat) : (term122 n) = (Peano.le n n).
Proof. exact (@lem3087812 (Peano.le n n)). Qed.
Lemma lem3087814 (n : nat) (h1 : term21) : Peano.le n n.
Proof. exact (EQ_MP (@lem3087813 n) (@lem3087810 n h1)). Qed.
Lemma lem3087816 (b : Prop) (a : Prop) : (a \/ b) = (term92 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3087817 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) : (term115 _32141 _32142 _32139 _32140) = (term124 _32142 _32140 _32139 _32141).
Proof. exact (@lem3087816 (term113 _32141 _32142 _32139 _32140) (term125 _32139 _32141)). Qed.
Lemma lem3087819 (a : Prop) (b : Prop) : (term94 a b) = (term95 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3087820 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term126 _32141 _32142 _32139 _32140) = (term127 _32141 _32142 _32139 _32140).
Proof. exact (@lem3087819 (term125 _32140 _32142) (term110 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087822 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3087823 (_32140 : nat) (_32142 : nat) : (term128 _32140 _32142) = (_32140 = _32142).
Proof. exact (@lem3087822 (_32140 = _32142)). Qed.
Lemma lem3087824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3087825 (_32140 : nat) (_32142 : nat) : (term129 _32140 _32142) = (term130 _32140 _32142).
Proof. exact (MK_COMB (@lem3087824) (@lem3087823 _32140 _32142)). Qed.
Lemma lem3087827 (a : Prop) (b : Prop) : (term94 a b) = (term95 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3087828 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term131 _32141 _32142 _32139 _32140) = (term132 _32141 _32142 _32139 _32140).
Proof. exact (@lem3087827 (Peano.le _32141 _32142) (term31 _32139 _32140)). Qed.
Lemma lem3087830 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3087831 (_32139 : nat) (_32140 : nat) : (term133 _32139 _32140) = (Peano.le _32139 _32140).
Proof. exact (@lem3087830 (Peano.le _32139 _32140)). Qed.
Lemma lem3087832 (_32141 : nat) (_32142 : nat) : (term134 _32141 _32142) = (term134 _32141 _32142).
Proof. exact (eq_refl (term134 _32141 _32142)). Qed.
Lemma lem3087833 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term132 _32141 _32142 _32139 _32140) = (term135 _32141 _32142 _32139 _32140).
Proof. exact (MK_COMB (@lem3087832 _32141 _32142) (@lem3087831 _32139 _32140)). Qed.
Lemma lem3087834 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term131 _32141 _32142 _32139 _32140) = (term135 _32141 _32142 _32139 _32140).
Proof. exact (TRANS (@lem3087828 _32141 _32142 _32139 _32140) (@lem3087833 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087835 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term127 _32141 _32142 _32139 _32140) = (term136 _32141 _32142 _32139 _32140).
Proof. exact (MK_COMB (@lem3087825 _32140 _32142) (@lem3087834 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087836 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term126 _32141 _32142 _32139 _32140) = (term136 _32141 _32142 _32139 _32140).
Proof. exact (TRANS (@lem3087820 _32141 _32142 _32139 _32140) (@lem3087835 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3087838 (_32141 : nat) (_32142 : nat) (_32139 : nat) (_32140 : nat) : (term137 _32141 _32142 _32139 _32140) = (term138 _32141 _32142 _32139 _32140).
Proof. exact (MK_COMB (@lem3087837) (@lem3087836 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087839 (_32139 : nat) (_32141 : nat) : (term125 _32139 _32141) = (term125 _32139 _32141).
Proof. exact (eq_refl (term125 _32139 _32141)). Qed.
Lemma lem3087840 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) : (term124 _32142 _32140 _32139 _32141) = (term139 _32142 _32140 _32139 _32141).
Proof. exact (MK_COMB (@lem3087838 _32141 _32142 _32139 _32140) (@lem3087839 _32139 _32141)). Qed.
Lemma lem3087841 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) : (term115 _32141 _32142 _32139 _32140) = (term139 _32142 _32140 _32139 _32141).
Proof. exact (TRANS (@lem3087817 _32142 _32140 _32139 _32141) (@lem3087840 _32142 _32140 _32139 _32141)). Qed.
Lemma lem3087843 (n : nat) (h1 : term21) (h2 : term65 n) : term140 n.
Proof. exact (conj (@lem3087806 n h2) (@lem3087814 n h1)). Qed.
Lemma lem3087844 (n : nat) (h1 : term21) (h2 : term65 n) : term141 n.
Proof. exact (conj (@lem3087798 n) (@lem3087843 n h1 h2)). Qed.
Lemma lem3087846 (_32142 : nat) (_32140 : nat) (_32139 : nat) (_32141 : nat) : term139 _32142 _32140 _32139 _32141.
Proof. exact (EQ_MP (@lem3087841 _32142 _32140 _32139 _32141) (@lem3087773 _32141 _32142 _32139 _32140)). Qed.
Lemma lem3087847 (n : nat) : term142 n.
Proof. exact (@lem3087846 n n n (NUMERAL 0)). Qed.
Lemma lem3087850 (n : nat) (h1 : term21) (h2 : term65 n) : term58 n.
Proof. exact (@lem3087847 n (@lem3087844 n h1 h2)). Qed.
Lemma lem3087851 (n : nat) (h1 : term21) (h2 : term65 n) : term143 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem3087850 n h1 h2). Qed.
Lemma lem3087853 (p : Prop) : (term78 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3087854 (n : nat) : (term143 n) = (term58 n).
Proof. exact (@lem3087853 (n = (NUMERAL 0))). Qed.
Lemma lem3087855 (n : nat) (h1 : term21) (h2 : term65 n) : term58 n.
Proof. exact (EQ_MP (@lem3087854 n) (@lem3087851 n h1 h2)). Qed.
Lemma lem3087861 (q : Prop) (p : Prop) (r : Prop) : (term79 p q r) = (term79 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3087862 (_32113 : nat) (_32114 : nat) : (term52 _32113 _32114) = (term80 _32113 _32114).
Proof. exact (@lem3087861 (Peano.le _32113 _32114) (term75 _32113 _32114) (_32114 = (NUMERAL 0))). Qed.
Lemma lem3087876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3087877 (_32113 : nat) (_32114 : nat) : (term81 _32113 _32114) = (term82 _32113 _32114).
Proof. exact (@lem3087876 (_32114 = (NUMERAL 0)) (term75 _32113 _32114)). Qed.
Lemma lem3087885 (_32113 : nat) (_32114 : nat) : (term83 _32113 _32114) = (term83 _32113 _32114).
Proof. exact (eq_refl (term83 _32113 _32114)). Qed.
Lemma lem3087886 (_32113 : nat) (_32114 : nat) : (term80 _32113 _32114) = (term84 _32113 _32114).
Proof. exact (MK_COMB (@lem3087885 _32113 _32114) (@lem3087877 _32113 _32114)). Qed.
Lemma lem3087897 (_32113 : nat) (_32114 : nat) : (term52 _32113 _32114) = (term84 _32113 _32114).
Proof. exact (TRANS (@lem3087862 _32113 _32114) (@lem3087886 _32113 _32114)). Qed.
Lemma lem3087898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3087899 (_32113 : nat) (_32114 : nat) : (term85 _32113 _32114) = (term86 _32113 _32114).
Proof. exact (MK_COMB (@lem3087898) (@lem3087897 _32113 _32114)). Qed.
Lemma lem3087913 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3087914 (_32113 : nat) (_32114 : nat) : (term81 _32113 _32114) = (term82 _32113 _32114).
Proof. exact (@lem3087913 (_32114 = (NUMERAL 0)) (term75 _32113 _32114)). Qed.
Lemma lem3087922 (_32113 : nat) (_32114 : nat) : (term83 _32113 _32114) = (term83 _32113 _32114).
Proof. exact (eq_refl (term83 _32113 _32114)). Qed.
Lemma lem3087923 (_32113 : nat) (_32114 : nat) : (term80 _32113 _32114) = (term84 _32113 _32114).
Proof. exact (MK_COMB (@lem3087922 _32113 _32114) (@lem3087914 _32113 _32114)). Qed.
Lemma lem3087934 (_32113 : nat) (_32114 : nat) : ((term52 _32113 _32114) = (term80 _32113 _32114)) = ((term84 _32113 _32114) = (term84 _32113 _32114)).
Proof. exact (MK_COMB (@lem3087899 _32113 _32114) (@lem3087923 _32113 _32114)). Qed.
Lemma lem3087936 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3087937 (x : Prop) : (x = x) = True.
Proof. exact (@lem3087936 Prop x). Qed.
Lemma lem3087938 (_32113 : nat) (_32114 : nat) : ((term84 _32113 _32114) = (term84 _32113 _32114)) = True.
Proof. exact (@lem3087937 (term84 _32113 _32114)). Qed.
Lemma lem3087939 (_32113 : nat) (_32114 : nat) : ((term52 _32113 _32114) = (term80 _32113 _32114)) = True.
Proof. exact (TRANS (@lem3087934 _32113 _32114) (@lem3087938 _32113 _32114)). Qed.
Lemma lem3087940 (_32113 : nat) (_32114 : nat) : True = ((term52 _32113 _32114) = (term80 _32113 _32114)).
Proof. exact (SYM (@lem3087939 _32113 _32114)). Qed.
Lemma lem3087941 (_32113 : nat) (_32114 : nat) : (term52 _32113 _32114) = (term80 _32113 _32114).
Proof. exact (EQ_MP (@lem3087940 _32113 _32114) (@lem0)). Qed.
Lemma lem3087942 (_32113 : nat) (_32114 : nat) (h1 : term10) : term80 _32113 _32114.
Proof. exact (EQ_MP (@lem3087941 _32113 _32114) (@lem3087499 _32113 _32114 h1)). Qed.
Lemma lem3087944 (b : Prop) (a : Prop) : (a \/ b) = (term92 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3087945 (_32113 : nat) (_32114 : nat) : (term80 _32113 _32114) = (term144 _32113 _32114).
Proof. exact (@lem3087944 (term81 _32113 _32114) (Peano.le _32113 _32114)). Qed.
Lemma lem3087947 (a : Prop) (b : Prop) : (term94 a b) = (term95 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3087948 (_32113 : nat) (_32114 : nat) : (term145 _32113 _32114) = (term146 _32113 _32114).
Proof. exact (@lem3087947 (term75 _32113 _32114) (_32114 = (NUMERAL 0))). Qed.
Lemma lem3087950 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3087951 (_32113 : nat) (_32114 : nat) : (term99 _32113 _32114) = (num_divides _32113 _32114).
Proof. exact (@lem3087950 (num_divides _32113 _32114)). Qed.
Lemma lem3087952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3087953 (_32113 : nat) (_32114 : nat) : (term100 _32113 _32114) = (term28 _32113 _32114).
Proof. exact (MK_COMB (@lem3087952) (@lem3087951 _32113 _32114)). Qed.
Lemma lem3087954 (_32114 : nat) : (term58 _32114) = (term58 _32114).
Proof. exact (eq_refl (term58 _32114)). Qed.
Lemma lem3087955 (_32113 : nat) (_32114 : nat) : (term146 _32113 _32114) = (term147 _32113 _32114).
Proof. exact (MK_COMB (@lem3087953 _32113 _32114) (@lem3087954 _32114)). Qed.
Lemma lem3087956 (_32113 : nat) (_32114 : nat) : (term145 _32113 _32114) = (term147 _32113 _32114).
Proof. exact (TRANS (@lem3087948 _32113 _32114) (@lem3087955 _32113 _32114)). Qed.
Lemma lem3087957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3087958 (_32113 : nat) (_32114 : nat) : (term148 _32113 _32114) = (term149 _32113 _32114).
Proof. exact (MK_COMB (@lem3087957) (@lem3087956 _32113 _32114)). Qed.
Lemma lem3087959 (_32113 : nat) (_32114 : nat) : (Peano.le _32113 _32114) = (Peano.le _32113 _32114).
Proof. exact (eq_refl (Peano.le _32113 _32114)). Qed.
Lemma lem3087960 (_32113 : nat) (_32114 : nat) : (term144 _32113 _32114) = (term150 _32113 _32114).
Proof. exact (MK_COMB (@lem3087958 _32113 _32114) (@lem3087959 _32113 _32114)). Qed.
Lemma lem3087961 (_32113 : nat) (_32114 : nat) : (term80 _32113 _32114) = (term150 _32113 _32114).
Proof. exact (TRANS (@lem3087945 _32113 _32114) (@lem3087960 _32113 _32114)). Qed.
Lemma lem3087963 (n : nat) (m : nat) (h1 : term21) (h2 : term65 n) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : term151 n.
Proof. exact (conj (@lem3087790 n m h3 h4) (@lem3087855 n h1 h2)). Qed.
Lemma lem3087965 (_32113 : nat) (_32114 : nat) (h1 : term10) : term150 _32113 _32114.
Proof. exact (EQ_MP (@lem3087961 _32113 _32114) (@lem3087942 _32113 _32114 h1)). Qed.
Lemma lem3087966 (n : nat) (h1 : term10) : term152 n.
Proof. exact (@lem3087965 (NUMERAL 0) n h1). Qed.
Lemma lem3087969 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term65 n) (h4 : term35 m n) (h5 : m = (NUMERAL 0)) : term121 n.
Proof. exact (@lem3087966 n h1 (@lem3087963 n m h2 h3 h4 h5)). Qed.
Lemma lem3087970 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : term153 n.
Proof. exact (fun h0 : term65 n => @lem3087969 n m h1 h2 h0 h3 h4). Qed.
Lemma lem3087972 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087973 (n : nat) : (term153 n) = (term121 n).
Proof. exact (@lem3087972 (term121 n)). Qed.
Lemma lem3087974 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : term121 n.
Proof. exact (EQ_MP (@lem3087973 n) (@lem3087970 n m h1 h2 h3 h4)). Qed.
Lemma lem3087977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3087979 (n : nat) : (term65 n) = (term154 n).
Proof. exact (@lem3087977 (term121 n)). Qed.
Lemma lem3087982 (n : nat) (m : nat) (h1 : term35 m n) (h2 : m = (NUMERAL 0)) : term154 n.
Proof. exact (EQ_MP (@lem3087979 n) (@lem3087512 n m h1 h2)). Qed.
Lemma lem3087985 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (@lem3087982 n m h3 h4 (@lem3087974 n m h1 h2 h3 h4)). Qed.
Lemma lem3087986 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : term107.
Proof. exact (fun h0 : ~ False => @lem3087985 n m h1 h2 h3 h4). Qed.
Lemma lem3087988 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3087989 : term107 = False.
Proof. exact (@lem3087988 False). Qed.
Lemma lem3087991 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem3087989) (@lem3087986 n m h1 h2 h3 h4)). Qed.
Lemma lem3087992 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem3087991 n m h1 h2 h3 h4) (fun h5 : False => @lem3087457 m h4)). Qed.
Lemma lem3087993 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem3087992 n m h1 h2 h3 h4) (@lem3087457 m h4)). Qed.
Lemma lem3087994 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : (term58 n) = False.
Proof. exact (prop_ext (fun h4 : term58 n => @lem3087735 m n h1 h2 h3) (fun h4 : False => @lem3087439 n h2)). Qed.
Lemma lem3087995 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3087994 m n h1 h2 h3) (@lem3087439 n h2)). Qed.
Lemma lem3087996 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem3087993 n m h1 h2 h3 h4) (fun h5 : False => @lem3087403 m h4)). Qed.
Lemma lem3087997 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem3087996 n m h1 h2 h3 h4) (@lem3087403 m h4)). Qed.
Lemma lem3087998 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : (term58 n) = False.
Proof. exact (prop_ext (fun h4 : term58 n => @lem3087995 m n h1 h2 h3) (fun h4 : False => @lem3087362 n h2)). Qed.
Lemma lem3087999 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3087998 m n h1 h2 h3) (@lem3087362 n h2)). Qed.
Lemma lem3088000 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem3087997 n m h1 h2 h3 h4) (fun h5 : False => @lem3087403 m h4)). Qed.
Lemma lem3088001 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem3088000 n m h1 h2 h3 h4) (@lem3087403 m h4)). Qed.
Lemma lem3088002 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : term21 = False.
Proof. exact (prop_ext (fun h5 : term21 => @lem3088001 n m h1 h2 h3 h4) (fun h5 : False => @lem3087369 h2)). Qed.
Lemma lem3088003 (n : nat) (m : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem3088002 n m h1 h2 h3 h4) (@lem3087369 h2)). Qed.
Lemma lem3088004 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : (term58 n) = False.
Proof. exact (prop_ext (fun h4 : term58 n => @lem3087999 m n h1 h2 h3) (fun h4 : False => @lem3087362 n h2)). Qed.
Lemma lem3088005 (m : nat) (n : nat) (h1 : term10) (h2 : term58 n) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3088004 m n h1 h2 h3) (@lem3087362 n h2)). Qed.
Lemma lem3088006 (m : nat) (n : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) : False.
Proof. exact (or_elim (@lem3087318 m n h3) (fun h0 : term58 n => @lem3088005 m n h1 h0 h3) (fun h0 : m = (NUMERAL 0) => @lem3088003 n m h1 h2 h3 h0)). Qed.
Lemma lem3088007 (m : nat) (n : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) : (term35 m n) = False.
Proof. exact (prop_ext (fun h4 : term35 m n => @lem3088006 m n h1 h2 h3) (fun h4 : False => @lem3087315 m n h3)). Qed.
Lemma lem3088008 (m : nat) (n : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3088007 m n h1 h2 h3) (@lem3087315 m n h3)). Qed.
Lemma lem3088009 (m : nat) (n : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem3088008 m n h1 h2 h3) (fun h4 : False => @lem3087245 h2)). Qed.
Lemma lem3088010 (m : nat) (n : nat) (h1 : term10) (h2 : term21) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem3088009 m n h1 h2 h3) (@lem3087245 h2)). Qed.
Lemma lem3088011 (m : nat) (h1 : term10) (h2 : term21) (h3 : term45 m) : False.
Proof. exact (ex_elim (@lem3087235 m h3) (fun n : nat => fun h0 : term44 m n => @lem3088010 m n h1 h2 h0)). Qed.
Lemma lem3088012 (h1 : term10) (h2 : term21) (h3 : term3) : False.
Proof. exact (ex_elim (@lem3087147 h3) (fun m : nat => fun h0 : term50 m => @lem3088011 m h1 h2 h0)). Qed.
Lemma lem3088013 (h1 : term10) (h2 : term21) (h3 : term3) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem3088012 h1 h2 h3) (fun h4 : False => @lem3087160 h2)). Qed.
Lemma lem3088014 (h1 : term10) (h2 : term21) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem3088013 h1 h2 h3) (@lem3087160 h2)). Qed.
Lemma lem3088015 (h1 : term21) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem3088014 h0 h1 h2). Qed.
Lemma lem3088016 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem3088017 (h1 : term21) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem3088016) (@lem3088015 h1 h2)). Qed.
Lemma lem3088018 (h1 : term3) : term13.
Proof. exact (fun h0 : term21 => @lem3088017 h0 h1). Qed.
Lemma lem3088019 : term15.
Proof. exact (fun h0 : term3 => @lem3088018 h0). Qed.
Lemma lem3088020 : term4.
Proof. exact (EQ_MP (@lem3087050) (@lem3088019)). Qed.
Lemma lem3088022 : term4.
Proof. exact (@lem3086905 (@lem3088020)). Qed.
Lemma lem3088023 (h1 : term3) : term12.
Proof. exact (@lem3088022 (@lem3086890 h1)). Qed.
Lemma lem3088024 (h1 : term3) : term8.
Proof. exact (@lem3088023 h1 (@lem91603)). Qed.
Lemma lem3088025 (h1 : term3) : False.
Proof. exact (@lem3088024 h1 (@lem3082292)). Qed.
Lemma lem3088026 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem3088025 h1) (fun h2 : False => @lem3086890 h1)). Qed.
Lemma lem3088027 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem3088026 h1) (@lem3086890 h1)). Qed.
Lemma lem3088028 : term2.
Proof. exact (fun h0 : term3 => @lem3088027 h0). Qed.
Lemma lem3088029 : term1.
Proof. exact (EQ_MP (@lem3086889) (@lem3088028)). Qed.
