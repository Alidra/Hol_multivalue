Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_BOOL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_BOOL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4594559 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4594560 : ((@CARD Prop (@UNIV Prop)) = term1) = term2.
Proof. exact (@lem4594559 ((@CARD Prop (@UNIV Prop)) = term1)). Qed.
Lemma lem4594561 : term2 = ((@CARD Prop (@UNIV Prop)) = term1).
Proof. exact (SYM (@lem4594560)). Qed.
Lemma lem4594562 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4594563 : term4.
Proof. exact (@lem3863773 Prop). Qed.
Lemma lem4594567 {_100044 : Type'} (h1 : term5 _100044) : term5 _100044.
Proof. exact (h1). Qed.
Lemma lem4594568 {_100044 : Type'} : term6 _100044.
Proof. exact (fun h0 : term5 _100044 => @lem4594567 _100044 h0). Qed.
Lemma lem4594569 {_100044 : Type'} (h1 : term6 _100044) : term6 _100044.
Proof. exact (h1). Qed.
Lemma lem4594570 {_100044 : Type'} (h1 : term5 _100044) : term5 _100044.
Proof. exact (h1). Qed.
Lemma lem4594571 {_100044 : Type'} (h1 : term5 _100044) (h2 : term6 _100044) : term5 _100044.
Proof. exact (@lem4594569 _100044 h2 (@lem4594570 _100044 h1)). Qed.
Lemma lem4594572 {_100044 : Type'} (h1 : term5 _100044) : term7 _100044.
Proof. exact (fun h0 : term6 _100044 => @lem4594571 _100044 h1 h0). Qed.
Lemma lem4594573 {_100044 : Type'} (h1 : term6 _100044) : term6 _100044.
Proof. exact (h1). Qed.
Lemma lem4594574 {_100044 : Type'} (h1 : term5 _100044) (h2 : term6 _100044) : term5 _100044.
Proof. exact (@lem4594572 _100044 h1 (@lem4594573 _100044 h2)). Qed.
Lemma lem4594575 {_100044 : Type'} (h1 : term6 _100044) : term6 _100044.
Proof. exact (fun h0 : term5 _100044 => @lem4594574 _100044 h0 h1). Qed.
Lemma lem4594576 {_100044 : Type'} : term8 _100044.
Proof. exact (fun h0 : term6 _100044 => @lem4594575 _100044 h0). Qed.
Lemma lem4594579 {_100044 : Type'} : term6 _100044.
Proof. exact (@lem4594576 _100044 (@lem4594568 _100044)). Qed.
Lemma lem4594580 {_100044 : Type'} : term6 _100044.
Proof. exact (@lem4594579 _100044). Qed.
Lemma lem4594608 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4594609 : term9 = term10.
Proof. exact (@lem4594608 term11). Qed.
Lemma lem4594610 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem4594611 : term13 = term14.
Proof. exact (MK_COMB (@lem4594610) (@lem4594609)). Qed.
Lemma lem4594614 {_100044 : Type'} : (term15 _100044) = (term15 _100044).
Proof. exact (eq_refl (term15 _100044)). Qed.
Lemma lem4594615 {_100044 : Type'} : (term16 _100044) = (term17 _100044).
Proof. exact (MK_COMB (@lem4594614 _100044) (@lem4594611)). Qed.
Lemma lem4594618 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem4594625 {_100044 : Type'} : (term5 _100044) = (term19 _100044).
Proof. exact (MK_COMB (@lem4594618) (@lem4594615 _100044)). Qed.
Lemma lem4594628 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem4594637 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term20 s n)) = ((@HAS_SIZE Prop s n) = (term20 s n)).
Proof. exact (eq_refl ((@HAS_SIZE Prop s n) = (term20 s n))). Qed.
Lemma lem4594638 (s : Prop -> Prop) : (term21 s) = (term21 s).
Proof. exact (fun_ext (fun n : nat => @lem4594637 s n)). Qed.
Lemma lem4594639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4594640 (s : Prop -> Prop) : (term22 s) = (term22 s).
Proof. exact (MK_COMB (@lem4594639) (@lem4594638 s)). Qed.
Lemma lem4594641 : term23 = term23.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4594640 s)). Qed.
Lemma lem4594642 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4594643 : term4 = term4.
Proof. exact (MK_COMB (@lem4594642) (@lem4594641)). Qed.
Lemma lem4594644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4594645 : term12 = term12.
Proof. exact (MK_COMB (@lem4594644) (@lem4594643)). Qed.
Lemma lem4594646 : term14 = term14.
Proof. exact (MK_COMB (@lem4594645) (@lem4594628)). Qed.
Lemma lem4594655 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term24 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term24 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term24 _100044 s n))). Qed.
Lemma lem4594656 {_100044 : Type'} (s : _100044 -> Prop) : (term25 _100044 s) = (term25 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem4594655 _100044 s n)). Qed.
Lemma lem4594657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4594658 {_100044 : Type'} (s : _100044 -> Prop) : (term26 _100044 s) = (term26 _100044 s).
Proof. exact (MK_COMB (@lem4594657) (@lem4594656 _100044 s)). Qed.
Lemma lem4594659 {_100044 : Type'} : (term27 _100044) = (term27 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem4594658 _100044 s)). Qed.
Lemma lem4594660 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem4594661 {_100044 : Type'} : (term28 _100044) = (term28 _100044).
Proof. exact (MK_COMB (@lem4594660 _100044) (@lem4594659 _100044)). Qed.
Lemma lem4594662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4594663 {_100044 : Type'} : (term15 _100044) = (term15 _100044).
Proof. exact (MK_COMB (@lem4594662) (@lem4594661 _100044)). Qed.
Lemma lem4594664 {_100044 : Type'} : (term17 _100044) = (term17 _100044).
Proof. exact (MK_COMB (@lem4594663 _100044) (@lem4594646)). Qed.
Lemma lem4594669 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem4594670 {_100044 : Type'} : (term19 _100044) = (term19 _100044).
Proof. exact (MK_COMB (@lem4594669) (@lem4594664 _100044)). Qed.
Lemma lem4594707 {_100044 : Type'} : (term5 _100044) = (term19 _100044).
Proof. exact (TRANS (@lem4594625 _100044) (@lem4594670 _100044)). Qed.
Lemma lem4594708 {_100044 : Type'} : (term19 _100044) = (term5 _100044).
Proof. exact (SYM (@lem4594707 _100044)). Qed.
Lemma lem4594711 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4594718 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4595026 (s : Prop -> Prop) (n : nat) : (term29 s n) = (term30 s n).
Proof. exact (@lem17045 (@FINITE Prop s) ((@CARD Prop s) = n)). Qed.
Lemma lem4595032 (s : Prop -> Prop) (n : nat) : (term31 s n) = (term31 s n).
Proof. exact (eq_refl (term31 s n)). Qed.
Lemma lem4595034 (s : Prop -> Prop) (n : nat) : (term32 s n) = (term32 s n).
Proof. exact (eq_refl (term32 s n)). Qed.
Lemma lem4595035 (s : Prop -> Prop) (n : nat) : (term33 s n) = (term34 s n).
Proof. exact (MK_COMB (@lem4595034 s n) (@lem4595026 s n)). Qed.
Lemma lem4595036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595037 (s : Prop -> Prop) (n : nat) : (term35 s n) = (term36 s n).
Proof. exact (MK_COMB (@lem4595036) (@lem4595035 s n)). Qed.
Lemma lem4595038 (s : Prop -> Prop) (n : nat) : (term37 s n) = (term38 s n).
Proof. exact (MK_COMB (@lem4595037 s n) (@lem4595032 s n)). Qed.
Lemma lem4595039 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term20 s n)) = (term37 s n).
Proof. exact (@lem17784 (@HAS_SIZE Prop s n) (term20 s n)). Qed.
Lemma lem4595040 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term20 s n)) = (term38 s n).
Proof. exact (TRANS (@lem4595039 s n) (@lem4595038 s n)). Qed.
Lemma lem4595041 (s : Prop -> Prop) : (term21 s) = (term39 s).
Proof. exact (fun_ext (fun n : nat => @lem4595040 s n)). Qed.
Lemma lem4595042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595043 (s : Prop -> Prop) : (term22 s) = (term40 s).
Proof. exact (MK_COMB (@lem4595042) (@lem4595041 s)). Qed.
Lemma lem4595044 : term23 = term41.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595043 s)). Qed.
Lemma lem4595045 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595046 : term4 = term42.
Proof. exact (MK_COMB (@lem4595045) (@lem4595044)). Qed.
Lemma lem4595052 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4595053 (P : nat -> Prop) (Q : nat -> Prop) : (term45 P Q) = (term46 P Q).
Proof. exact (@lem4595052 nat P Q). Qed.
Lemma lem4595054 (s : Prop -> Prop) : (term47 s) = (term48 s).
Proof. exact (@lem4595053 (term49 s) (term50 s)). Qed.
Lemma lem4595055 (s : Prop -> Prop) (n : nat) : (term51 s n) = (term34 s n).
Proof. exact (eq_refl (term51 s n)). Qed.
Lemma lem4595056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595057 (s : Prop -> Prop) (n : nat) : (term52 s n) = (term36 s n).
Proof. exact (MK_COMB (@lem4595056) (@lem4595055 s n)). Qed.
Lemma lem4595058 (s : Prop -> Prop) (n : nat) : (term53 s n) = (term31 s n).
Proof. exact (eq_refl (term53 s n)). Qed.
Lemma lem4595059 (s : Prop -> Prop) (n : nat) : (term54 s n) = (term38 s n).
Proof. exact (MK_COMB (@lem4595057 s n) (@lem4595058 s n)). Qed.
Lemma lem4595060 (s : Prop -> Prop) : (term55 s) = (term39 s).
Proof. exact (fun_ext (fun n : nat => @lem4595059 s n)). Qed.
Lemma lem4595061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595062 (s : Prop -> Prop) : (term47 s) = (term40 s).
Proof. exact (MK_COMB (@lem4595061) (@lem4595060 s)). Qed.
Lemma lem4595063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4595064 (s : Prop -> Prop) : (term56 s) = (term57 s).
Proof. exact (MK_COMB (@lem4595063) (@lem4595062 s)). Qed.
Lemma lem4595065 (s : Prop -> Prop) (n : nat) : (term51 s n) = (term34 s n).
Proof. exact (eq_refl (term51 s n)). Qed.
Lemma lem4595066 (s : Prop -> Prop) : (term58 s) = (term49 s).
Proof. exact (fun_ext (fun n : nat => @lem4595065 s n)). Qed.
Lemma lem4595067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595068 (s : Prop -> Prop) : (term59 s) = (term60 s).
Proof. exact (MK_COMB (@lem4595067) (@lem4595066 s)). Qed.
Lemma lem4595069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595070 (s : Prop -> Prop) : (term61 s) = (term62 s).
Proof. exact (MK_COMB (@lem4595069) (@lem4595068 s)). Qed.
Lemma lem4595071 (s : Prop -> Prop) (n : nat) : (term53 s n) = (term31 s n).
Proof. exact (eq_refl (term53 s n)). Qed.
Lemma lem4595072 (s : Prop -> Prop) : (term63 s) = (term50 s).
Proof. exact (fun_ext (fun n : nat => @lem4595071 s n)). Qed.
Lemma lem4595073 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595074 (s : Prop -> Prop) : (term64 s) = (term65 s).
Proof. exact (MK_COMB (@lem4595073) (@lem4595072 s)). Qed.
Lemma lem4595075 (s : Prop -> Prop) : (term48 s) = (term66 s).
Proof. exact (MK_COMB (@lem4595070 s) (@lem4595074 s)). Qed.
Lemma lem4595076 (s : Prop -> Prop) : ((term47 s) = (term48 s)) = ((term40 s) = (term66 s)).
Proof. exact (MK_COMB (@lem4595064 s) (@lem4595075 s)). Qed.
Lemma lem4595077 (s : Prop -> Prop) : (term40 s) = (term66 s).
Proof. exact (EQ_MP (@lem4595076 s) (@lem4595054 s)). Qed.
Lemma lem4595174 : term41 = term67.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595077 s)). Qed.
Lemma lem4595175 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595176 : term42 = term68.
Proof. exact (MK_COMB (@lem4595175) (@lem4595174)). Qed.
Lemma lem4595178 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4595179 (P : type920) (Q : type920) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem4595178 (Prop -> Prop) P Q). Qed.
Lemma lem4595180 : term71 = term72.
Proof. exact (@lem4595179 term73 term74). Qed.
Lemma lem4595181 (s : Prop -> Prop) : (term75 s) = (term60 s).
Proof. exact (eq_refl (term75 s)). Qed.
Lemma lem4595182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595183 (s : Prop -> Prop) : (term76 s) = (term62 s).
Proof. exact (MK_COMB (@lem4595182) (@lem4595181 s)). Qed.
Lemma lem4595184 (s : Prop -> Prop) : (term77 s) = (term65 s).
Proof. exact (eq_refl (term77 s)). Qed.
Lemma lem4595185 (s : Prop -> Prop) : (term78 s) = (term66 s).
Proof. exact (MK_COMB (@lem4595183 s) (@lem4595184 s)). Qed.
Lemma lem4595186 : term79 = term67.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595185 s)). Qed.
Lemma lem4595187 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595188 : term71 = term68.
Proof. exact (MK_COMB (@lem4595187) (@lem4595186)). Qed.
Lemma lem4595189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4595190 : term80 = term81.
Proof. exact (MK_COMB (@lem4595189) (@lem4595188)). Qed.
Lemma lem4595191 (s : Prop -> Prop) : (term75 s) = (term60 s).
Proof. exact (eq_refl (term75 s)). Qed.
Lemma lem4595192 : term82 = term73.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595191 s)). Qed.
Lemma lem4595193 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595194 : term83 = term84.
Proof. exact (MK_COMB (@lem4595193) (@lem4595192)). Qed.
Lemma lem4595195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595196 : term85 = term86.
Proof. exact (MK_COMB (@lem4595195) (@lem4595194)). Qed.
Lemma lem4595197 (s : Prop -> Prop) : (term77 s) = (term65 s).
Proof. exact (eq_refl (term77 s)). Qed.
Lemma lem4595198 : term87 = term74.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595197 s)). Qed.
Lemma lem4595199 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595200 : term88 = term89.
Proof. exact (MK_COMB (@lem4595199) (@lem4595198)). Qed.
Lemma lem4595201 : term72 = term90.
Proof. exact (MK_COMB (@lem4595196) (@lem4595200)). Qed.
Lemma lem4595202 : (term71 = term72) = (term68 = term90).
Proof. exact (MK_COMB (@lem4595190) (@lem4595201)). Qed.
Lemma lem4595203 : term68 = term90.
Proof. exact (EQ_MP (@lem4595202) (@lem4595180)). Qed.
Lemma lem4595310 : term42 = term90.
Proof. exact (TRANS (@lem4595176) (@lem4595203)). Qed.
Lemma lem4595311 : term4 = term90.
Proof. exact (TRANS (@lem4595046) (@lem4595310)). Qed.
Lemma lem4595312 (h1 : term4) : term90.
Proof. exact (EQ_MP (@lem4595311) (@lem4594711 h1)). Qed.
Lemma lem4595318 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4595334 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4595421 (s : Prop -> Prop) (n : nat) : (term31 s n) = (term31 s n).
Proof. exact (eq_refl (term31 s n)). Qed.
Lemma lem4595422 (s : Prop -> Prop) : (term50 s) = (term50 s).
Proof. exact (fun_ext (fun n : nat => @lem4595421 s n)). Qed.
Lemma lem4595423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595424 (s : Prop -> Prop) : (term65 s) = (term65 s).
Proof. exact (MK_COMB (@lem4595423) (@lem4595422 s)). Qed.
Lemma lem4595425 : term74 = term74.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595424 s)). Qed.
Lemma lem4595426 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595427 : term89 = term89.
Proof. exact (MK_COMB (@lem4595426) (@lem4595425)). Qed.
Lemma lem4595452 (s : Prop -> Prop) (n : nat) : (term34 s n) = (term34 s n).
Proof. exact (eq_refl (term34 s n)). Qed.
Lemma lem4595453 (s : Prop -> Prop) : (term49 s) = (term49 s).
Proof. exact (fun_ext (fun n : nat => @lem4595452 s n)). Qed.
Lemma lem4595454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595455 (s : Prop -> Prop) : (term60 s) = (term60 s).
Proof. exact (MK_COMB (@lem4595454) (@lem4595453 s)). Qed.
Lemma lem4595456 : term73 = term73.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595455 s)). Qed.
Lemma lem4595457 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595458 : term84 = term84.
Proof. exact (MK_COMB (@lem4595457) (@lem4595456)). Qed.
Lemma lem4595459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4595460 : term86 = term86.
Proof. exact (MK_COMB (@lem4595459) (@lem4595458)). Qed.
Lemma lem4595461 : term90 = term90.
Proof. exact (MK_COMB (@lem4595460) (@lem4595427)). Qed.
Lemma lem4595462 (h1 : term4) : term90.
Proof. exact (EQ_MP (@lem4595461) (@lem4595312 h1)). Qed.
Lemma lem4595474 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4595475 (h1 : term4) : term89.
Proof. exact (proj2 (@lem4595462 h1)). Qed.
Lemma lem4595482 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4595486 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4595526 (s : Prop -> Prop) (n : nat) : (term31 s n) = (term91 s n).
Proof. exact (@lem19490 (@FINITE Prop s) (term92 s n) ((@CARD Prop s) = n)). Qed.
Lemma lem4595527 (s : Prop -> Prop) : (term50 s) = (term93 s).
Proof. exact (fun_ext (fun n : nat => @lem4595526 s n)). Qed.
Lemma lem4595528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595529 (s : Prop -> Prop) : (term65 s) = (term94 s).
Proof. exact (MK_COMB (@lem4595528) (@lem4595527 s)). Qed.
Lemma lem4595530 : term74 = term95.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595529 s)). Qed.
Lemma lem4595531 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595533 : term89 = term96.
Proof. exact (MK_COMB (@lem4595531) (@lem4595530)). Qed.
Lemma lem4595534 (h1 : term4) : term96.
Proof. exact (EQ_MP (@lem4595533) (@lem4595475 h1)). Qed.
Lemma lem4595589 (_55163 : Prop -> Prop) (h1 : term4) : term97 _55163.
Proof. exact (@lem4595534 h1 _55163). Qed.
Lemma lem4595590 (_55163 : Prop -> Prop) : (term97 _55163) = (term94 _55163).
Proof. exact (eq_refl (term97 _55163)). Qed.
Lemma lem4595591 (_55163 : Prop -> Prop) (h1 : term4) : term94 _55163.
Proof. exact (EQ_MP (@lem4595590 _55163) (@lem4595589 _55163 h1)). Qed.
Lemma lem4595592 (_55163 : Prop -> Prop) (_55164 : nat) (h1 : term4) : term98 _55163 _55164.
Proof. exact (@lem4595591 _55163 h1 _55164). Qed.
Lemma lem4595593 (_55163 : Prop -> Prop) (_55164 : nat) : (term98 _55163 _55164) = (term91 _55163 _55164).
Proof. exact (eq_refl (term98 _55163 _55164)). Qed.
Lemma lem4595594 (_55163 : Prop -> Prop) (_55164 : nat) (h1 : term4) : term91 _55163 _55164.
Proof. exact (EQ_MP (@lem4595593 _55163 _55164) (@lem4595592 _55163 _55164 h1)). Qed.
Lemma lem4595612 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4595614 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4595658 (_55163 : Prop -> Prop) (_55164 : nat) (h1 : term4) : term99 _55163 _55164.
Proof. exact (proj2 (@lem4595594 _55163 _55164 h1)). Qed.
Lemma lem4595768 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4595769 (h1 : term11) : term100.
Proof. exact (fun h0 : term10 => @lem4595768 h1). Qed.
Lemma lem4595771 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4595772 : term100 = term11.
Proof. exact (@lem4595771 term11). Qed.
Lemma lem4595773 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem4595772) (@lem4595769 h1)). Qed.
Lemma lem4595779 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4595780 (_55163 : Prop -> Prop) (_55164 : nat) : (term99 _55163 _55164) = (term102 _55163 _55164).
Proof. exact (@lem4595779 ((@CARD Prop _55163) = _55164) (term92 _55163 _55164)). Qed.
Lemma lem4595788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4595789 (_55163 : Prop -> Prop) (_55164 : nat) : (term103 _55163 _55164) = (term104 _55163 _55164).
Proof. exact (MK_COMB (@lem4595788) (@lem4595780 _55163 _55164)). Qed.
Lemma lem4595797 (_55163 : Prop -> Prop) (_55164 : nat) : (term102 _55163 _55164) = (term102 _55163 _55164).
Proof. exact (eq_refl (term102 _55163 _55164)). Qed.
Lemma lem4595798 (_55163 : Prop -> Prop) (_55164 : nat) : ((term99 _55163 _55164) = (term102 _55163 _55164)) = ((term102 _55163 _55164) = (term102 _55163 _55164)).
Proof. exact (MK_COMB (@lem4595789 _55163 _55164) (@lem4595797 _55163 _55164)). Qed.
Lemma lem4595800 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4595801 (x : Prop) : (x = x) = True.
Proof. exact (@lem4595800 Prop x). Qed.
Lemma lem4595802 (_55163 : Prop -> Prop) (_55164 : nat) : ((term102 _55163 _55164) = (term102 _55163 _55164)) = True.
Proof. exact (@lem4595801 (term102 _55163 _55164)). Qed.
Lemma lem4595803 (_55163 : Prop -> Prop) (_55164 : nat) : ((term99 _55163 _55164) = (term102 _55163 _55164)) = True.
Proof. exact (TRANS (@lem4595798 _55163 _55164) (@lem4595802 _55163 _55164)). Qed.
Lemma lem4595804 (_55163 : Prop -> Prop) (_55164 : nat) : True = ((term99 _55163 _55164) = (term102 _55163 _55164)).
Proof. exact (SYM (@lem4595803 _55163 _55164)). Qed.
Lemma lem4595805 (_55163 : Prop -> Prop) (_55164 : nat) : (term99 _55163 _55164) = (term102 _55163 _55164).
Proof. exact (EQ_MP (@lem4595804 _55163 _55164) (@lem0)). Qed.
Lemma lem4595806 (_55163 : Prop -> Prop) (_55164 : nat) (h1 : term4) : term102 _55163 _55164.
Proof. exact (EQ_MP (@lem4595805 _55163 _55164) (@lem4595658 _55163 _55164 h1)). Qed.
Lemma lem4595808 (b : Prop) (a : Prop) : (a \/ b) = (term105 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4595809 (_55163 : Prop -> Prop) (_55164 : nat) : (term102 _55163 _55164) = (term106 _55163 _55164).
Proof. exact (@lem4595808 (term92 _55163 _55164) ((@CARD Prop _55163) = _55164)). Qed.
Lemma lem4595811 (a : Prop) : (term107 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4595812 (_55163 : Prop -> Prop) (_55164 : nat) : (term108 _55163 _55164) = (@HAS_SIZE Prop _55163 _55164).
Proof. exact (@lem4595811 (@HAS_SIZE Prop _55163 _55164)). Qed.
Lemma lem4595813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4595814 (_55163 : Prop -> Prop) (_55164 : nat) : (term109 _55163 _55164) = (term110 _55163 _55164).
Proof. exact (MK_COMB (@lem4595813) (@lem4595812 _55163 _55164)). Qed.
Lemma lem4595815 (_55163 : Prop -> Prop) (_55164 : nat) : ((@CARD Prop _55163) = _55164) = ((@CARD Prop _55163) = _55164).
Proof. exact (eq_refl ((@CARD Prop _55163) = _55164)). Qed.
Lemma lem4595816 (_55163 : Prop -> Prop) (_55164 : nat) : (term106 _55163 _55164) = (term111 _55163 _55164).
Proof. exact (MK_COMB (@lem4595814 _55163 _55164) (@lem4595815 _55163 _55164)). Qed.
Lemma lem4595817 (_55163 : Prop -> Prop) (_55164 : nat) : (term102 _55163 _55164) = (term111 _55163 _55164).
Proof. exact (TRANS (@lem4595809 _55163 _55164) (@lem4595816 _55163 _55164)). Qed.
Lemma lem4595820 (_55163 : Prop -> Prop) (_55164 : nat) (h1 : term4) : term111 _55163 _55164.
Proof. exact (EQ_MP (@lem4595817 _55163 _55164) (@lem4595806 _55163 _55164 h1)). Qed.
Lemma lem4595821 (h1 : term4) : term112.
Proof. exact (@lem4595820 (@UNIV Prop) term1 h1). Qed.
Lemma lem4595824 (h1 : term4) (h2 : term11) : (@CARD Prop (@UNIV Prop)) = term1.
Proof. exact (@lem4595821 h1 (@lem4595773 h2)). Qed.
Lemma lem4595825 (h1 : term4) (h2 : term11) : term113.
Proof. exact (fun h0 : term3 => @lem4595824 h1 h2). Qed.
Lemma lem4595827 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4595828 : term113 = ((@CARD Prop (@UNIV Prop)) = term1).
Proof. exact (@lem4595827 ((@CARD Prop (@UNIV Prop)) = term1)). Qed.
Lemma lem4595829 (h1 : term4) (h2 : term11) : (@CARD Prop (@UNIV Prop)) = term1.
Proof. exact (EQ_MP (@lem4595828) (@lem4595825 h1 h2)). Qed.
Lemma lem4595832 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4595834 : term3 = term114.
Proof. exact (@lem4595832 ((@CARD Prop (@UNIV Prop)) = term1)). Qed.
Lemma lem4595837 (h1 : term3) : term114.
Proof. exact (EQ_MP (@lem4595834) (@lem4595612 h1)). Qed.
Lemma lem4595840 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (@lem4595837 h2 (@lem4595829 h1 h3)). Qed.
Lemma lem4595841 (h1 : term4) (h2 : term3) (h3 : term11) : term115.
Proof. exact (fun h0 : ~ False => @lem4595840 h1 h2 h3). Qed.
Lemma lem4595843 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4595844 : term115 = False.
Proof. exact (@lem4595843 False). Qed.
Lemma lem4595845 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595844) (@lem4595841 h1 h2 h3)). Qed.
Lemma lem4595846 (h1 : term4) (h2 : term3) (h3 : term11) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem4595845 h1 h2 h3) (fun h4 : False => @lem4595614 h3)). Qed.
Lemma lem4595847 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595846 h1 h2 h3) (@lem4595614 h3)). Qed.
Lemma lem4595848 (h1 : term4) (h2 : term3) (h3 : term11) : term3 = False.
Proof. exact (prop_ext (fun h4 : term3 => @lem4595847 h1 h2 h3) (fun h4 : False => @lem4595612 h2)). Qed.
Lemma lem4595849 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595848 h1 h2 h3) (@lem4595612 h2)). Qed.
Lemma lem4595850 (h1 : term4) (h2 : term3) (h3 : term11) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem4595849 h1 h2 h3) (fun h4 : False => @lem4595486 h3)). Qed.
Lemma lem4595851 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595850 h1 h2 h3) (@lem4595486 h3)). Qed.
Lemma lem4595852 (h1 : term4) (h2 : term3) (h3 : term11) : term3 = False.
Proof. exact (prop_ext (fun h4 : term3 => @lem4595851 h1 h2 h3) (fun h4 : False => @lem4595482 h2)). Qed.
Lemma lem4595853 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595852 h1 h2 h3) (@lem4595482 h2)). Qed.
Lemma lem4595854 (h1 : term4) (h2 : term3) (h3 : term11) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem4595853 h1 h2 h3) (fun h4 : False => @lem4595486 h3)). Qed.
Lemma lem4595855 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595854 h1 h2 h3) (@lem4595486 h3)). Qed.
Lemma lem4595856 (h1 : term4) (h2 : term3) (h3 : term11) : term3 = False.
Proof. exact (prop_ext (fun h4 : term3 => @lem4595855 h1 h2 h3) (fun h4 : False => @lem4595482 h2)). Qed.
Lemma lem4595857 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595856 h1 h2 h3) (@lem4595482 h2)). Qed.
Lemma lem4595858 (h1 : term4) (h2 : term3) (h3 : term11) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem4595857 h1 h2 h3) (fun h4 : False => @lem4595474 h3)). Qed.
Lemma lem4595859 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595858 h1 h2 h3) (@lem4595474 h3)). Qed.
Lemma lem4595860 (h1 : term4) (h2 : term3) (h3 : term11) : term3 = False.
Proof. exact (prop_ext (fun h4 : term3 => @lem4595859 h1 h2 h3) (fun h4 : False => @lem4595334 h2)). Qed.
Lemma lem4595861 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595860 h1 h2 h3) (@lem4595334 h2)). Qed.
Lemma lem4595862 (h1 : term4) (h2 : term3) (h3 : term11) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem4595861 h1 h2 h3) (fun h4 : False => @lem4595318 h3)). Qed.
Lemma lem4595863 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595862 h1 h2 h3) (@lem4595318 h3)). Qed.
Lemma lem4595864 (h1 : term4) (h2 : term3) (h3 : term11) : term3 = False.
Proof. exact (prop_ext (fun h4 : term3 => @lem4595863 h1 h2 h3) (fun h4 : False => @lem4594718 h2)). Qed.
Lemma lem4595865 (h1 : term4) (h2 : term3) (h3 : term11) : False.
Proof. exact (EQ_MP (@lem4595864 h1 h2 h3) (@lem4594718 h2)). Qed.
Lemma lem4595866 (h1 : term4) (h2 : term3) : term9.
Proof. exact (fun h0 : term11 => @lem4595865 h1 h2 h0). Qed.
Lemma lem4595867 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem4595868 (h1 : term4) (h2 : term3) : term10.
Proof. exact (EQ_MP (@lem4595867) (@lem4595866 h1 h2)). Qed.
Lemma lem4595869 (h1 : term3) : term14.
Proof. exact (fun h0 : term4 => @lem4595868 h0 h1). Qed.
Lemma lem4595870 {_100044 : Type'} (h1 : term3) : term17 _100044.
Proof. exact (fun h0 : term28 _100044 => @lem4595869 h1). Qed.
Lemma lem4595871 {_100044 : Type'} : term19 _100044.
Proof. exact (fun h0 : term3 => @lem4595870 _100044 h0). Qed.
Lemma lem4595872 {_100044 : Type'} : term5 _100044.
Proof. exact (EQ_MP (@lem4594708 _100044) (@lem4595871 _100044)). Qed.
Lemma lem4595874 {_100044 : Type'} : term5 _100044.
Proof. exact (@lem4594580 _100044 (@lem4595872 _100044)). Qed.
Lemma lem4595875 {_100044 : Type'} (h1 : term3) : term16 _100044.
Proof. exact (@lem4595874 _100044 (@lem4594562 h1)). Qed.
Lemma lem4595876 (h1 : term3) : term13.
Proof. exact (@lem4595875 Prop h1 (@lem3863773 Prop)). Qed.
Lemma lem4595877 (h1 : term3) : term9.
Proof. exact (@lem4595876 h1 (@lem4594563)). Qed.
Lemma lem4595878 (h1 : term3) : False.
Proof. exact (@lem4595877 h1 (@lem4594547)). Qed.
Lemma lem4595879 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem4595878 h1) (fun h2 : False => @lem4594562 h1)). Qed.
Lemma lem4595880 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem4595879 h1) (@lem4594562 h1)). Qed.
Lemma lem4595881 : term2.
Proof. exact (fun h0 : term3 => @lem4595880 h0). Qed.
Lemma lem4595882 : (@CARD Prop (@UNIV Prop)) = term1.
Proof. exact (EQ_MP (@lem4594561) (@lem4595881)). Qed.
