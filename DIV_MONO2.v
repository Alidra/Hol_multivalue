Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MONO2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import LE_spec.
Require Import LE_ADD_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_TRANS_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem210832 (n : nat) : term0 n.
Proof. exact (@lem157261 n). Qed.
Lemma lem210833 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem210834 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem210833 n) (@lem210832 n)). Qed.
Lemma lem210835 (n : nat) (m : nat) : term2 n m.
Proof. exact (@lem210834 n m). Qed.
Lemma lem210836 (n : nat) (m : nat) : (term2 n m) = (term3 n m).
Proof. exact (eq_refl (term2 n m)). Qed.
Lemma lem210837 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem210836 n m) (@lem210835 n m)). Qed.
Lemma lem210838 (m : nat) : term4 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem210839 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem210840 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem210839 m) (@lem210838 m)). Qed.
Lemma lem210841 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem210840 m n). Qed.
Lemma lem210842 (n : nat) (m : nat) : (term6 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem210844 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem210845 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem210844 h1 m). Qed.
Lemma lem210846 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem210847 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem210846 m) (@lem210845 m h1)). Qed.
Lemma lem210848 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem210847 m h1 n). Qed.
Lemma lem210849 (n : nat) (m : nat) : (term10 m n) = (term11 n m).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem210850 (n : nat) (m : nat) (h1 : term7) : term11 n m.
Proof. exact (EQ_MP (@lem210849 n m) (@lem210848 m n h1)). Qed.
Lemma lem210851 (n : nat) (m : nat) (p : nat) (h1 : term7) : term12 n m p.
Proof. exact (@lem210850 n m h1 p). Qed.
Lemma lem210852 (n : nat) (m : nat) (p : nat) : (term12 n m p) = (term13 n m p).
Proof. exact (eq_refl (term12 n m p)). Qed.
Lemma lem210853 (n : nat) (m : nat) (p : nat) (h1 : term7) : term13 n m p.
Proof. exact (EQ_MP (@lem210852 n m p) (@lem210851 n m p h1)). Qed.
Lemma lem210854 (m : nat) (n : nat) (p : nat) (h1 : term14 m n p) : term14 m n p.
Proof. exact (h1). Qed.
Lemma lem210855 (m : nat) (n : nat) (p : nat) (h1 : term7) (h2 : term14 m n p) : Peano.le m p.
Proof. exact (@lem210853 n m p h1 (@lem210854 m n p h2)). Qed.
Lemma lem210856 (m : nat) (n : nat) (p : nat) (h1 : term14 m n p) : term15 m p.
Proof. exact (fun h0 : term7 => @lem210855 m n p h0 h1). Qed.
Lemma lem210857 (m : nat) (p : nat) (h1 : term16 m p) : term16 m p.
Proof. exact (h1). Qed.
Lemma lem210858 (m : nat) (p : nat) (h1 : term16 m p) : term15 m p.
Proof. exact (ex_elim (@lem210857 m p h1) (fun n : nat => fun h0 : term17 m p n => @lem210856 m n p h0)). Qed.
Lemma lem210859 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem210860 (m : nat) (p : nat) (h1 : term7) (h2 : term16 m p) : Peano.le m p.
Proof. exact (@lem210858 m p h2 (@lem210859 h1)). Qed.
Lemma lem210861 (m : nat) (p : nat) (h1 : term7) : term18 m p.
Proof. exact (fun h0 : term16 m p => @lem210860 m p h1 h0). Qed.
Lemma lem210862 (m : nat) (h1 : term7) : term19 m.
Proof. exact (fun p : nat => @lem210861 m p h1). Qed.
Lemma lem210863 (h1 : term7) : term20.
Proof. exact (fun m : nat => @lem210862 m h1). Qed.
Lemma lem210864 : term21.
Proof. exact (fun h0 : term7 => @lem210863 h0). Qed.
Lemma lem210865 : term20.
Proof. exact (@lem210864 (@lem93743)). Qed.
Lemma lem210866 (m : nat) : term22 m.
Proof. exact (@lem210865 m). Qed.
Lemma lem210867 (m : nat) : (term22 m) = (term19 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem210868 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem210867 m) (@lem210866 m)). Qed.
Lemma lem210869 (m : nat) (p : nat) : term23 m p.
Proof. exact (@lem210868 m p). Qed.
Lemma lem210870 (m : nat) (p : nat) : (term23 m p) = (term18 m p).
Proof. exact (eq_refl (term23 m p)). Qed.
Lemma lem210872 (p : nat) (m : nat) (h1 : term24 p m) : term24 p m.
Proof. exact (h1). Qed.
Lemma lem210873 (p : nat) (m : nat) (h1 : Peano.le p m) : Peano.le p m.
Proof. exact (h1). Qed.
Lemma lem210874 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem210875 (a : nat) : term26 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem210876 (a : nat) : (term26 a) = (term27 a).
Proof. exact (eq_refl (term26 a)). Qed.
Lemma lem210877 (a : nat) : term27 a.
Proof. exact (EQ_MP (@lem210876 a) (@lem210875 a)). Qed.
Lemma lem210878 (a : nat) (b : nat) : term28 a b.
Proof. exact (@lem210877 a b). Qed.
Lemma lem210879 (a : nat) (b : nat) : (term28 a b) = (term29 a b).
Proof. exact (eq_refl (term28 a b)). Qed.
Lemma lem210880 (a : nat) (b : nat) : term29 a b.
Proof. exact (EQ_MP (@lem210879 a b) (@lem210878 a b)). Qed.
Lemma lem210881 (a : nat) (b : nat) (n : nat) : term30 a b n.
Proof. exact (@lem210880 a b n). Qed.
Lemma lem210882 (a : nat) (n : nat) (b : nat) : (term30 a b n) = (term31 a n b).
Proof. exact (eq_refl (term30 a b n)). Qed.
Lemma lem210883 (a : nat) (n : nat) (b : nat) : term31 a n b.
Proof. exact (EQ_MP (@lem210882 a n b) (@lem210881 a b n)). Qed.
Lemma lem210884 (a : nat) (h1 : term25 a) : term25 a.
Proof. exact (h1). Qed.
Lemma lem210885 (n : nat) (b : nat) (a : nat) (h1 : term25 a) : (term32 n b a) = (term33 a n b).
Proof. exact (@lem210883 a n b (@lem210884 a h1)). Qed.
Lemma lem210891 (p : nat) : term34 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem210907 (a : nat) (n : nat) (b : nat) : term31 a n b.
Proof. exact (fun h0 : term25 a => @lem210885 n b a h0). Qed.
Lemma lem210908 (p : nat) (m : nat) (n : nat) : term35 p m n.
Proof. exact (@lem210907 p (Nat.div n m) n). Qed.
Lemma lem210910 (p : nat) (h1 : term25 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem210891 p (@lem210874 p h1)). Qed.
Lemma lem210911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem210912 (p : nat) (h1 : term25 p) : (term25 p) = (~ False).
Proof. exact (MK_COMB (@lem210911) (@lem210910 p h1)). Qed.
Lemma lem210914 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem210915 (p : nat) (h1 : term25 p) : (term25 p) = True.
Proof. exact (TRANS (@lem210912 p h1) (@lem210914)). Qed.
Lemma lem210916 (p : nat) (h1 : term25 p) : True = (term25 p).
Proof. exact (SYM (@lem210915 p h1)). Qed.
Lemma lem210917 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (EQ_MP (@lem210916 p h1) (@lem0)). Qed.
Lemma lem210918 (m : nat) (n : nat) (p : nat) (h1 : term25 p) : (term36 m n p) = (term37 p m n).
Proof. exact (@lem210908 p m n (@lem210917 p h1)). Qed.
Lemma lem210919 (m : nat) (n : nat) (p : nat) (h1 : term25 p) : (term37 p m n) = (term36 m n p).
Proof. exact (SYM (@lem210918 m n p h1)). Qed.
Lemma lem210921 (m : nat) (p : nat) : term18 m p.
Proof. exact (EQ_MP (@lem210870 m p) (@lem210869 m p)). Qed.
Lemma lem210922 (p : nat) (m : nat) (n : nat) : term38 p m n.
Proof. exact (@lem210921 (term39 p n m) n). Qed.
Lemma lem210923 (m : nat) : term40 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem210924 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem210925 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem210924 m) (@lem210923 m)). Qed.
Lemma lem210926 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem210925 m n). Qed.
Lemma lem210927 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem210928 (m : nat) (n : nat) : term43 m n.
Proof. exact (EQ_MP (@lem210927 m n) (@lem210926 m n)). Qed.
Lemma lem210929 (m : nat) (n : nat) (p : nat) : term44 m n p.
Proof. exact (@lem210928 m n p). Qed.
Lemma lem210930 (m : nat) (n : nat) (p : nat) : (term44 m n p) = ((term45 m n p) = (term46 m n p)).
Proof. exact (eq_refl (term44 m n p)). Qed.
Lemma lem210945 (p : nat) (m : nat) : (Peano.le p m) = ((Peano.le p m) = True).
Proof. exact (@lem7 (Peano.le p m)). Qed.
Lemma lem210950 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (EQ_MP (@lem210930 m n p) (@lem210929 m n p)). Qed.
Lemma lem210951 (p : nat) (n : nat) (m : nat) : (term47 p n m) = (term48 p n m).
Proof. exact (@lem210950 p m (Nat.div n m)). Qed.
Lemma lem210955 (p : nat) (m : nat) (h1 : Peano.le p m) : (Peano.le p m) = True.
Proof. exact (EQ_MP (@lem210945 p m) (@lem210873 p m h1)). Qed.
Lemma lem210956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem210957 (p : nat) (m : nat) (h1 : Peano.le p m) : (term49 p m) = (or True).
Proof. exact (MK_COMB (@lem210956) (@lem210955 p m h1)). Qed.
Lemma lem210960 (n : nat) (m : nat) : ((Nat.div n m) = (NUMERAL 0)) = ((Nat.div n m) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.div n m) = (NUMERAL 0))). Qed.
Lemma lem210961 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term48 p n m) = (term50 n m).
Proof. exact (MK_COMB (@lem210957 p m h1) (@lem210960 n m)). Qed.
Lemma lem210963 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem210964 (n : nat) (m : nat) : (term50 n m) = True.
Proof. exact (@lem210963 ((Nat.div n m) = (NUMERAL 0))). Qed.
Lemma lem210965 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term48 p n m) = True.
Proof. exact (TRANS (@lem210961 n p m h1) (@lem210964 n m)). Qed.
Lemma lem210966 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term47 p n m) = True.
Proof. exact (TRANS (@lem210951 p n m) (@lem210965 n p m h1)). Qed.
Lemma lem210967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem210968 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term51 p n m) = (and True).
Proof. exact (MK_COMB (@lem210967) (@lem210966 n p m h1)). Qed.
Lemma lem210969 (m : nat) (n : nat) : (term52 m n) = (term52 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem210970 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term53 p m n) = (term54 m n).
Proof. exact (MK_COMB (@lem210968 n p m h1) (@lem210969 m n)). Qed.
Lemma lem210972 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem210973 (m : nat) (n : nat) : (term54 m n) = (term52 m n).
Proof. exact (@lem210972 (term52 m n)). Qed.
Lemma lem210974 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term53 p m n) = (term52 m n).
Proof. exact (TRANS (@lem210970 n p m h1) (@lem210973 m n)). Qed.
Lemma lem210975 (n : nat) (p : nat) (m : nat) (h1 : Peano.le p m) : (term52 m n) = (term53 p m n).
Proof. exact (SYM (@lem210974 n p m h1)). Qed.
Lemma lem210977 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem210842 n m) (@lem210841 m n)). Qed.
Lemma lem210978 (n : nat) (m : nat) : (term55 n m) = (term56 n m).
Proof. exact (@lem210977 (Nat.div n m) m). Qed.
Lemma lem210979 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem210980 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem210979) (@lem210978 n m)). Qed.
Lemma lem210981 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem210982 (m : nat) (n : nat) : (term52 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem210980 n m) (@lem210981 n)). Qed.
Lemma lem210983 (m : nat) (n : nat) : (term59 m n) = (term52 m n).
Proof. exact (SYM (@lem210982 m n)). Qed.
Lemma lem210985 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem210986 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (@lem210985 (term61 m n)). Qed.
Lemma lem210987 (m : nat) (n : nat) : (term62 m n) = (term61 m n).
Proof. exact (SYM (@lem210986 m n)). Qed.
Lemma lem210988 (m : nat) (n : nat) (h1 : term63 m n) : term63 m n.
Proof. exact (h1). Qed.
Lemma lem210991 (p : nat) (m : nat) (n : nat) (h1 : term64 p m n) : term64 p m n.
Proof. exact (h1). Qed.
Lemma lem210992 (p : nat) (m : nat) (n : nat) : term65 p m n.
Proof. exact (fun h0 : term64 p m n => @lem210991 p m n h0). Qed.
Lemma lem210993 (p : nat) (m : nat) (n : nat) (h1 : term65 p m n) : term65 p m n.
Proof. exact (h1). Qed.
Lemma lem210994 (p : nat) (m : nat) (n : nat) (h1 : term64 p m n) : term64 p m n.
Proof. exact (h1). Qed.
Lemma lem210995 (p : nat) (m : nat) (n : nat) (h1 : term64 p m n) (h2 : term65 p m n) : term64 p m n.
Proof. exact (@lem210993 p m n h2 (@lem210994 p m n h1)). Qed.
Lemma lem210996 (p : nat) (m : nat) (n : nat) (h1 : term64 p m n) : term66 p m n.
Proof. exact (fun h0 : term65 p m n => @lem210995 p m n h1 h0). Qed.
Lemma lem210997 (p : nat) (m : nat) (n : nat) (h1 : term65 p m n) : term65 p m n.
Proof. exact (h1). Qed.
Lemma lem210998 (p : nat) (m : nat) (n : nat) (h1 : term64 p m n) (h2 : term65 p m n) : term64 p m n.
Proof. exact (@lem210996 p m n h1 (@lem210997 p m n h2)). Qed.
Lemma lem210999 (p : nat) (m : nat) (n : nat) (h1 : term65 p m n) : term65 p m n.
Proof. exact (fun h0 : term64 p m n => @lem210998 p m n h0 h1). Qed.
Lemma lem211000 (p : nat) (m : nat) (n : nat) : term67 p m n.
Proof. exact (fun h0 : term65 p m n => @lem210999 p m n h0). Qed.
Lemma lem211003 (p : nat) (m : nat) (n : nat) : term65 p m n.
Proof. exact (@lem211000 p m n (@lem210992 p m n)). Qed.
Lemma lem211047 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem211048 : term68 = term69.
Proof. exact (@lem211047 term70). Qed.
Lemma lem211057 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem211058 : term72 = term73.
Proof. exact (MK_COMB (@lem211057) (@lem211048)). Qed.
Lemma lem211061 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem211062 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem211061 m n) (@lem211058)). Qed.
Lemma lem211065 (p : nat) (m : nat) : (term77 p m) = (term77 p m).
Proof. exact (eq_refl (term77 p m)). Qed.
Lemma lem211066 (p : nat) (m : nat) (n : nat) : (term78 p m n) = (term79 p m n).
Proof. exact (MK_COMB (@lem211065 p m) (@lem211062 m n)). Qed.
Lemma lem211069 (p : nat) : (term80 p) = (term80 p).
Proof. exact (eq_refl (term80 p)). Qed.
Lemma lem211070 (p : nat) (m : nat) (n : nat) : (term64 p m n) = (term81 p m n).
Proof. exact (MK_COMB (@lem211069 p) (@lem211066 p m n)). Qed.
Lemma lem211073 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (fun_ext (fun p : nat => @lem211070 p m n)). Qed.
Lemma lem211074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211075 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem211074) (@lem211073 m n)). Qed.
Lemma lem211080 (n : nat) : (term86 n) = (term87 n).
Proof. exact (fun_ext (fun m : nat => @lem211075 m n)). Qed.
Lemma lem211081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211082 (n : nat) : (term88 n) = (term89 n).
Proof. exact (MK_COMB (@lem211081) (@lem211080 n)). Qed.
Lemma lem211087 : term90 = term91.
Proof. exact (fun_ext (fun n : nat => @lem211082 n)). Qed.
Lemma lem211088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211097 : term92 = term93.
Proof. exact (MK_COMB (@lem211088) (@lem211087)). Qed.
Lemma lem211098 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem211099 (m : nat) : (term95 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem211098 m n)). Qed.
Lemma lem211100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211101 (m : nat) : (term96 m) = (term96 m).
Proof. exact (MK_COMB (@lem211100) (@lem211099 m)). Qed.
Lemma lem211102 : term97 = term97.
Proof. exact (fun_ext (fun m : nat => @lem211101 m)). Qed.
Lemma lem211103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211104 : term70 = term70.
Proof. exact (MK_COMB (@lem211103) (@lem211102)). Qed.
Lemma lem211105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem211106 : term69 = term69.
Proof. exact (MK_COMB (@lem211105) (@lem211104)). Qed.
Lemma lem211115 (m : nat) (n : nat) : ((term98 m n) = (term99 m n)) = ((term98 m n) = (term99 m n)).
Proof. exact (eq_refl ((term98 m n) = (term99 m n))). Qed.
Lemma lem211116 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem211115 m n)). Qed.
Lemma lem211117 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211118 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem211117) (@lem211116 m)). Qed.
Lemma lem211119 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem211118 m)). Qed.
Lemma lem211120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211121 : term103 = term103.
Proof. exact (MK_COMB (@lem211120) (@lem211119)). Qed.
Lemma lem211126 (m : nat) : ((term104 m) = (m = (NUMERAL 0))) = ((term104 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term104 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem211127 : term105 = term105.
Proof. exact (fun_ext (fun m : nat => @lem211126 m)). Qed.
Lemma lem211128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211129 : term106 = term106.
Proof. exact (MK_COMB (@lem211128) (@lem211127)). Qed.
Lemma lem211130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211131 : term107 = term107.
Proof. exact (MK_COMB (@lem211130) (@lem211129)). Qed.
Lemma lem211132 : term108 = term108.
Proof. exact (MK_COMB (@lem211131) (@lem211121)). Qed.
Lemma lem211133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem211134 : term71 = term71.
Proof. exact (MK_COMB (@lem211133) (@lem211132)). Qed.
Lemma lem211135 : term73 = term73.
Proof. exact (MK_COMB (@lem211134) (@lem211106)). Qed.
Lemma lem211154 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem211155 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem211154 m n) (@lem211135)). Qed.
Lemma lem211158 (p : nat) (m : nat) : (term77 p m) = (term77 p m).
Proof. exact (eq_refl (term77 p m)). Qed.
Lemma lem211159 (p : nat) (m : nat) (n : nat) : (term79 p m n) = (term79 p m n).
Proof. exact (MK_COMB (@lem211158 p m) (@lem211155 m n)). Qed.
Lemma lem211164 (p : nat) : (term80 p) = (term80 p).
Proof. exact (eq_refl (term80 p)). Qed.
Lemma lem211165 (p : nat) (m : nat) (n : nat) : (term81 p m n) = (term81 p m n).
Proof. exact (MK_COMB (@lem211164 p) (@lem211159 p m n)). Qed.
Lemma lem211166 (m : nat) (n : nat) : (term83 m n) = (term83 m n).
Proof. exact (fun_ext (fun p : nat => @lem211165 p m n)). Qed.
Lemma lem211167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211168 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem211167) (@lem211166 m n)). Qed.
Lemma lem211169 (n : nat) : (term87 n) = (term87 n).
Proof. exact (fun_ext (fun m : nat => @lem211168 m n)). Qed.
Lemma lem211170 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211171 (n : nat) : (term89 n) = (term89 n).
Proof. exact (MK_COMB (@lem211170) (@lem211169 n)). Qed.
Lemma lem211172 : term91 = term91.
Proof. exact (fun_ext (fun n : nat => @lem211171 n)). Qed.
Lemma lem211173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211174 : term93 = term93.
Proof. exact (MK_COMB (@lem211173) (@lem211172)). Qed.
Lemma lem211243 : term92 = term93.
Proof. exact (TRANS (@lem211097) (@lem211174)). Qed.
Lemma lem211244 : term93 = term92.
Proof. exact (SYM (@lem211243)). Qed.
Lemma lem211247 (m : nat) (n : nat) (h1 : term63 m n) : term63 m n.
Proof. exact (h1). Qed.
Lemma lem211248 (h1 : term108) : term108.
Proof. exact (h1). Qed.
Lemma lem211249 (h1 : term70) : term70.
Proof. exact (h1). Qed.
Lemma lem211255 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem211261 (p : nat) (m : nat) (h1 : Peano.le p m) : Peano.le p m.
Proof. exact (h1). Qed.
Lemma lem211264 (m : nat) : (term109 m) = (m = (NUMERAL 0)).
Proof. exact (@lem16933 (m = (NUMERAL 0))). Qed.
Lemma lem211269 (n : nat) (m : nat) : (term110 n m) = (term110 n m).
Proof. exact (eq_refl (term110 n m)). Qed.
Lemma lem211270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem211271 (m : nat) : (term111 m) = (term112 m).
Proof. exact (MK_COMB (@lem211270) (@lem211264 m)). Qed.
Lemma lem211272 (n : nat) (m : nat) : (term113 n m) = (term114 n m).
Proof. exact (MK_COMB (@lem211271 m) (@lem211269 n m)). Qed.
Lemma lem211273 (n : nat) (m : nat) : (term3 n m) = (term113 n m).
Proof. exact (@lem17265 (term25 m) (term110 n m)). Qed.
Lemma lem211274 (n : nat) (m : nat) : (term3 n m) = (term114 n m).
Proof. exact (TRANS (@lem211273 n m) (@lem211272 n m)). Qed.
Lemma lem211275 (m : nat) (n : nat) : (term115 m n) = (term115 m n).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem211276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211277 (n : nat) (m : nat) : (term116 n m) = (term117 n m).
Proof. exact (MK_COMB (@lem211276) (@lem211274 n m)). Qed.
Lemma lem211278 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (MK_COMB (@lem211277 n m) (@lem211275 m n)). Qed.
Lemma lem211279 (m : nat) (n : nat) : (term63 m n) = (term118 m n).
Proof. exact (@lem17362 (term3 n m) (term59 m n)). Qed.
Lemma lem211284 (m : nat) (n : nat) : (term63 m n) = (term119 m n).
Proof. exact (TRANS (@lem211279 m n) (@lem211278 m n)). Qed.
Lemma lem211300 (m : nat) : ((term104 m) = (m = (NUMERAL 0))) = (term120 m).
Proof. exact (@lem17784 (term104 m) (m = (NUMERAL 0))). Qed.
Lemma lem211301 : term105 = term121.
Proof. exact (fun_ext (fun m : nat => @lem211300 m)). Qed.
Lemma lem211302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211303 : term106 = term122.
Proof. exact (MK_COMB (@lem211302) (@lem211301)). Qed.
Lemma lem211314 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (@lem17160 (m = (S n)) (Peano.le m n)). Qed.
Lemma lem211320 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem211322 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem211323 (m : nat) (n : nat) : (term127 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem211322 m n) (@lem211314 m n)). Qed.
Lemma lem211324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211325 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem211324) (@lem211323 m n)). Qed.
Lemma lem211326 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem211325 m n) (@lem211320 m n)). Qed.
Lemma lem211327 (m : nat) (n : nat) : ((term98 m n) = (term99 m n)) = (term131 m n).
Proof. exact (@lem17784 (term98 m n) (term99 m n)). Qed.
Lemma lem211328 (m : nat) (n : nat) : ((term98 m n) = (term99 m n)) = (term132 m n).
Proof. exact (TRANS (@lem211327 m n) (@lem211326 m n)). Qed.
Lemma lem211329 (m : nat) : (term100 m) = (term133 m).
Proof. exact (fun_ext (fun n : nat => @lem211328 m n)). Qed.
Lemma lem211330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211331 (m : nat) : (term101 m) = (term134 m).
Proof. exact (MK_COMB (@lem211330) (@lem211329 m)). Qed.
Lemma lem211332 : term102 = term135.
Proof. exact (fun_ext (fun m : nat => @lem211331 m)). Qed.
Lemma lem211333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211334 : term103 = term136.
Proof. exact (MK_COMB (@lem211333) (@lem211332)). Qed.
Lemma lem211335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211336 : term107 = term137.
Proof. exact (MK_COMB (@lem211335) (@lem211303)). Qed.
Lemma lem211337 : term108 = term138.
Proof. exact (MK_COMB (@lem211336) (@lem211334)). Qed.
Lemma lem211339 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem211340 (P : nat -> Prop) (Q : nat -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem211339 nat P Q). Qed.
Lemma lem211341 : term143 = term144.
Proof. exact (@lem211340 term145 term146). Qed.
Lemma lem211342 (m : nat) : (term147 m) = (term148 m).
Proof. exact (eq_refl (term147 m)). Qed.
Lemma lem211343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211344 (m : nat) : (term149 m) = (term150 m).
Proof. exact (MK_COMB (@lem211343) (@lem211342 m)). Qed.
Lemma lem211345 (m : nat) : (term151 m) = (term152 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem211346 (m : nat) : (term153 m) = (term120 m).
Proof. exact (MK_COMB (@lem211344 m) (@lem211345 m)). Qed.
Lemma lem211347 : term154 = term121.
Proof. exact (fun_ext (fun m : nat => @lem211346 m)). Qed.
Lemma lem211348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211349 : term143 = term122.
Proof. exact (MK_COMB (@lem211348) (@lem211347)). Qed.
Lemma lem211350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem211351 : term155 = term156.
Proof. exact (MK_COMB (@lem211350) (@lem211349)). Qed.
Lemma lem211352 (m : nat) : (term147 m) = (term148 m).
Proof. exact (eq_refl (term147 m)). Qed.
Lemma lem211353 : term157 = term145.
Proof. exact (fun_ext (fun m : nat => @lem211352 m)). Qed.
Lemma lem211354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211355 : term158 = term159.
Proof. exact (MK_COMB (@lem211354) (@lem211353)). Qed.
Lemma lem211356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211357 : term160 = term161.
Proof. exact (MK_COMB (@lem211356) (@lem211355)). Qed.
Lemma lem211358 (m : nat) : (term151 m) = (term152 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem211359 : term162 = term146.
Proof. exact (fun_ext (fun m : nat => @lem211358 m)). Qed.
Lemma lem211360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211361 : term163 = term164.
Proof. exact (MK_COMB (@lem211360) (@lem211359)). Qed.
Lemma lem211362 : term144 = term165.
Proof. exact (MK_COMB (@lem211357) (@lem211361)). Qed.
Lemma lem211363 : (term143 = term144) = (term122 = term165).
Proof. exact (MK_COMB (@lem211351) (@lem211362)). Qed.
Lemma lem211364 : term122 = term165.
Proof. exact (EQ_MP (@lem211363) (@lem211341)). Qed.
Lemma lem211461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211462 : term137 = term166.
Proof. exact (MK_COMB (@lem211461) (@lem211364)). Qed.
Lemma lem211468 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem211469 (P : nat -> Prop) (Q : nat -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem211468 nat P Q). Qed.
Lemma lem211470 (m : nat) : (term167 m) = (term168 m).
Proof. exact (@lem211469 (term169 m) (term170 m)). Qed.
Lemma lem211471 (m : nat) (n : nat) : (term171 m n) = (term128 m n).
Proof. exact (eq_refl (term171 m n)). Qed.
Lemma lem211472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211473 (m : nat) (n : nat) : (term172 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem211472) (@lem211471 m n)). Qed.
Lemma lem211474 (m : nat) (n : nat) : (term173 m n) = (term125 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem211475 (m : nat) (n : nat) : (term174 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem211473 m n) (@lem211474 m n)). Qed.
Lemma lem211476 (m : nat) : (term175 m) = (term133 m).
Proof. exact (fun_ext (fun n : nat => @lem211475 m n)). Qed.
Lemma lem211477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211478 (m : nat) : (term167 m) = (term134 m).
Proof. exact (MK_COMB (@lem211477) (@lem211476 m)). Qed.
Lemma lem211479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem211480 (m : nat) : (term176 m) = (term177 m).
Proof. exact (MK_COMB (@lem211479) (@lem211478 m)). Qed.
Lemma lem211481 (m : nat) (n : nat) : (term171 m n) = (term128 m n).
Proof. exact (eq_refl (term171 m n)). Qed.
Lemma lem211482 (m : nat) : (term178 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem211481 m n)). Qed.
Lemma lem211483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211484 (m : nat) : (term179 m) = (term180 m).
Proof. exact (MK_COMB (@lem211483) (@lem211482 m)). Qed.
Lemma lem211485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211486 (m : nat) : (term181 m) = (term182 m).
Proof. exact (MK_COMB (@lem211485) (@lem211484 m)). Qed.
Lemma lem211487 (m : nat) (n : nat) : (term173 m n) = (term125 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem211488 (m : nat) : (term183 m) = (term170 m).
Proof. exact (fun_ext (fun n : nat => @lem211487 m n)). Qed.
Lemma lem211489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211490 (m : nat) : (term184 m) = (term185 m).
Proof. exact (MK_COMB (@lem211489) (@lem211488 m)). Qed.
Lemma lem211491 (m : nat) : (term168 m) = (term186 m).
Proof. exact (MK_COMB (@lem211486 m) (@lem211490 m)). Qed.
Lemma lem211492 (m : nat) : ((term167 m) = (term168 m)) = ((term134 m) = (term186 m)).
Proof. exact (MK_COMB (@lem211480 m) (@lem211491 m)). Qed.
Lemma lem211493 (m : nat) : (term134 m) = (term186 m).
Proof. exact (EQ_MP (@lem211492 m) (@lem211470 m)). Qed.
Lemma lem211590 : term135 = term187.
Proof. exact (fun_ext (fun m : nat => @lem211493 m)). Qed.
Lemma lem211591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211592 : term136 = term188.
Proof. exact (MK_COMB (@lem211591) (@lem211590)). Qed.
Lemma lem211594 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem211595 (P : nat -> Prop) (Q : nat -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem211594 nat P Q). Qed.
Lemma lem211596 : term189 = term190.
Proof. exact (@lem211595 term191 term192). Qed.
Lemma lem211597 (m : nat) : (term193 m) = (term180 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem211598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211599 (m : nat) : (term194 m) = (term182 m).
Proof. exact (MK_COMB (@lem211598) (@lem211597 m)). Qed.
Lemma lem211600 (m : nat) : (term195 m) = (term185 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem211601 (m : nat) : (term196 m) = (term186 m).
Proof. exact (MK_COMB (@lem211599 m) (@lem211600 m)). Qed.
Lemma lem211602 : term197 = term187.
Proof. exact (fun_ext (fun m : nat => @lem211601 m)). Qed.
Lemma lem211603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211604 : term189 = term188.
Proof. exact (MK_COMB (@lem211603) (@lem211602)). Qed.
Lemma lem211605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem211606 : term198 = term199.
Proof. exact (MK_COMB (@lem211605) (@lem211604)). Qed.
Lemma lem211607 (m : nat) : (term193 m) = (term180 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem211608 : term200 = term191.
Proof. exact (fun_ext (fun m : nat => @lem211607 m)). Qed.
Lemma lem211609 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211610 : term201 = term202.
Proof. exact (MK_COMB (@lem211609) (@lem211608)). Qed.
Lemma lem211611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211612 : term203 = term204.
Proof. exact (MK_COMB (@lem211611) (@lem211610)). Qed.
Lemma lem211613 (m : nat) : (term195 m) = (term185 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem211614 : term205 = term192.
Proof. exact (fun_ext (fun m : nat => @lem211613 m)). Qed.
Lemma lem211615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211616 : term206 = term207.
Proof. exact (MK_COMB (@lem211615) (@lem211614)). Qed.
Lemma lem211617 : term190 = term208.
Proof. exact (MK_COMB (@lem211612) (@lem211616)). Qed.
Lemma lem211618 : (term189 = term190) = (term188 = term208).
Proof. exact (MK_COMB (@lem211606) (@lem211617)). Qed.
Lemma lem211619 : term188 = term208.
Proof. exact (EQ_MP (@lem211618) (@lem211596)). Qed.
Lemma lem211724 : term136 = term208.
Proof. exact (TRANS (@lem211592) (@lem211619)). Qed.
Lemma lem211727 : term138 = term209.
Proof. exact (MK_COMB (@lem211462) (@lem211724)). Qed.
Lemma lem211728 : term108 = term209.
Proof. exact (TRANS (@lem211337) (@lem211727)). Qed.
Lemma lem211729 (h1 : term108) : term209.
Proof. exact (EQ_MP (@lem211728) (@lem211248 h1)). Qed.
Lemma lem211730 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem211731 (m : nat) : (term95 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem211730 m n)). Qed.
Lemma lem211732 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211733 (m : nat) : (term96 m) = (term96 m).
Proof. exact (MK_COMB (@lem211732) (@lem211731 m)). Qed.
Lemma lem211734 : term97 = term97.
Proof. exact (fun_ext (fun m : nat => @lem211733 m)). Qed.
Lemma lem211735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211748 : term70 = term70.
Proof. exact (MK_COMB (@lem211735) (@lem211734)). Qed.
Lemma lem211749 (h1 : term70) : term70.
Proof. exact (EQ_MP (@lem211748) (@lem211249 h1)). Qed.
Lemma lem211759 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem211765 (p : nat) (m : nat) (h1 : Peano.le p m) : Peano.le p m.
Proof. exact (h1). Qed.
Lemma lem211827 (m : nat) (n : nat) (h1 : term63 m n) : term119 m n.
Proof. exact (EQ_MP (@lem211284 m n) (@lem211247 m n h1)). Qed.
Lemma lem211854 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem211855 (m : nat) : (term170 m) = (term170 m).
Proof. exact (fun_ext (fun n : nat => @lem211854 m n)). Qed.
Lemma lem211856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211857 (m : nat) : (term185 m) = (term185 m).
Proof. exact (MK_COMB (@lem211856) (@lem211855 m)). Qed.
Lemma lem211858 : term192 = term192.
Proof. exact (fun_ext (fun m : nat => @lem211857 m)). Qed.
Lemma lem211859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211860 : term207 = term207.
Proof. exact (MK_COMB (@lem211859) (@lem211858)). Qed.
Lemma lem211889 (m : nat) (n : nat) : (term128 m n) = (term128 m n).
Proof. exact (eq_refl (term128 m n)). Qed.
Lemma lem211890 (m : nat) : (term169 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem211889 m n)). Qed.
Lemma lem211891 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211892 (m : nat) : (term180 m) = (term180 m).
Proof. exact (MK_COMB (@lem211891) (@lem211890 m)). Qed.
Lemma lem211893 : term191 = term191.
Proof. exact (fun_ext (fun m : nat => @lem211892 m)). Qed.
Lemma lem211894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211895 : term202 = term202.
Proof. exact (MK_COMB (@lem211894) (@lem211893)). Qed.
Lemma lem211896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211897 : term204 = term204.
Proof. exact (MK_COMB (@lem211896) (@lem211895)). Qed.
Lemma lem211898 : term208 = term208.
Proof. exact (MK_COMB (@lem211897) (@lem211860)). Qed.
Lemma lem211917 (m : nat) : (term152 m) = (term152 m).
Proof. exact (eq_refl (term152 m)). Qed.
Lemma lem211918 : term146 = term146.
Proof. exact (fun_ext (fun m : nat => @lem211917 m)). Qed.
Lemma lem211919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211920 : term164 = term164.
Proof. exact (MK_COMB (@lem211919) (@lem211918)). Qed.
Lemma lem211939 (m : nat) : (term148 m) = (term148 m).
Proof. exact (eq_refl (term148 m)). Qed.
Lemma lem211940 : term145 = term145.
Proof. exact (fun_ext (fun m : nat => @lem211939 m)). Qed.
Lemma lem211941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211942 : term159 = term159.
Proof. exact (MK_COMB (@lem211941) (@lem211940)). Qed.
Lemma lem211943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211944 : term161 = term161.
Proof. exact (MK_COMB (@lem211943) (@lem211942)). Qed.
Lemma lem211945 : term165 = term165.
Proof. exact (MK_COMB (@lem211944) (@lem211920)). Qed.
Lemma lem211946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem211947 : term166 = term166.
Proof. exact (MK_COMB (@lem211946) (@lem211945)). Qed.
Lemma lem211948 : term209 = term209.
Proof. exact (MK_COMB (@lem211947) (@lem211898)). Qed.
Lemma lem211949 (h1 : term108) : term209.
Proof. exact (EQ_MP (@lem211948) (@lem211729 h1)). Qed.
Lemma lem211958 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem211959 (m : nat) : (term95 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem211958 m n)). Qed.
Lemma lem211960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211961 (m : nat) : (term96 m) = (term96 m).
Proof. exact (MK_COMB (@lem211960) (@lem211959 m)). Qed.
Lemma lem211962 : term97 = term97.
Proof. exact (fun_ext (fun m : nat => @lem211961 m)). Qed.
Lemma lem211963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem211964 : term70 = term70.
Proof. exact (MK_COMB (@lem211963) (@lem211962)). Qed.
Lemma lem211965 (h1 : term70) : term70.
Proof. exact (EQ_MP (@lem211964) (@lem211749 h1)). Qed.
Lemma lem211967 (h1 : term108) : term165.
Proof. exact (proj1 (@lem211949 h1)). Qed.
Lemma lem211970 (h1 : term108) : term164.
Proof. exact (proj2 (@lem211967 h1)). Qed.
Lemma lem211973 (m : nat) (n : nat) (h1 : term63 m n) : term114 n m.
Proof. exact (proj1 (@lem211827 m n h1)). Qed.
Lemma lem211975 (n : nat) (m : nat) (h1 : term110 n m) : term110 n m.
Proof. exact (h1). Qed.
Lemma lem211981 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem211985 (p : nat) (m : nat) (h1 : Peano.le p m) : Peano.le p m.
Proof. exact (h1). Qed.
Lemma lem212064 (m : nat) : (term152 m) = (term152 m).
Proof. exact (eq_refl (term152 m)). Qed.
Lemma lem212065 : term146 = term146.
Proof. exact (fun_ext (fun m : nat => @lem212064 m)). Qed.
Lemma lem212066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem212068 : term164 = term164.
Proof. exact (MK_COMB (@lem212066) (@lem212065)). Qed.
Lemma lem212069 (h1 : term108) : term164.
Proof. exact (EQ_MP (@lem212068) (@lem211970 h1)). Qed.
Lemma lem212077 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem212087 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem212088 (m : nat) : (term95 m) = (term95 m).
Proof. exact (fun_ext (fun n : nat => @lem212087 m n)). Qed.
Lemma lem212089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem212090 (m : nat) : (term96 m) = (term96 m).
Proof. exact (MK_COMB (@lem212089) (@lem212088 m)). Qed.
Lemma lem212091 : term97 = term97.
Proof. exact (fun_ext (fun m : nat => @lem212090 m)). Qed.
Lemma lem212092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem212094 : term70 = term70.
Proof. exact (MK_COMB (@lem212092) (@lem212091)). Qed.
Lemma lem212095 (h1 : term70) : term70.
Proof. exact (EQ_MP (@lem212094) (@lem211965 h1)). Qed.
Lemma lem212203 (_4246 : nat) (h1 : term108) : term151 _4246.
Proof. exact (@lem212069 h1 _4246). Qed.
Lemma lem212204 (_4246 : nat) : (term151 _4246) = (term152 _4246).
Proof. exact (eq_refl (term151 _4246)). Qed.
Lemma lem212206 (_4247 : nat) (h1 : term70) : term210 _4247.
Proof. exact (@lem212095 h1 _4247). Qed.
Lemma lem212207 (_4247 : nat) : (term210 _4247) = (term96 _4247).
Proof. exact (eq_refl (term210 _4247)). Qed.
Lemma lem212208 (_4247 : nat) (h1 : term70) : term96 _4247.
Proof. exact (EQ_MP (@lem212207 _4247) (@lem212206 _4247 h1)). Qed.
Lemma lem212209 (_4247 : nat) (_4248 : nat) (h1 : term70) : term211 _4247 _4248.
Proof. exact (@lem212208 _4247 h1 _4248). Qed.
Lemma lem212210 (_4247 : nat) (_4248 : nat) : (term211 _4247 _4248) = (term94 _4247 _4248).
Proof. exact (eq_refl (term211 _4247 _4248)). Qed.
Lemma lem212235 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem212237 (p : nat) (m : nat) (h1 : Peano.le p m) : Peano.le p m.
Proof. exact (h1). Qed.
Lemma lem212265 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem212307 (m : nat) (n : nat) (h1 : term63 m n) : term115 m n.
Proof. exact (proj2 (@lem211827 m n h1)). Qed.
Lemma lem212351 (p : nat) (h1 : term25 p) : term25 p.
Proof. exact (h1). Qed.
Lemma lem212352 (p : nat) : (term212 p) = (term212 p).
Proof. exact (eq_refl (term212 p)). Qed.
Lemma lem212353 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term213 p m) = (term214 p).
Proof. exact (MK_COMB (@lem212352 p) (@lem212265 m h1)). Qed.
Lemma lem212354 (p : nat) : (term214 p) = (term104 p).
Proof. exact (eq_refl (term214 p)). Qed.
Lemma lem212355 (p : nat) (m : nat) : (term215 p m) = (term215 p m).
Proof. exact (eq_refl (term215 p m)). Qed.
Lemma lem212356 (m : nat) (p : nat) : ((term213 p m) = (term214 p)) = ((term213 p m) = (term104 p)).
Proof. exact (MK_COMB (@lem212355 p m) (@lem212354 p)). Qed.
Lemma lem212357 (p : nat) (m : nat) : (term213 p m) = (Peano.le p m).
Proof. exact (eq_refl (term213 p m)). Qed.
Lemma lem212358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem212359 (p : nat) (m : nat) : (term215 p m) = (term216 p m).
Proof. exact (MK_COMB (@lem212358) (@lem212357 p m)). Qed.
Lemma lem212360 (p : nat) : (term104 p) = (term104 p).
Proof. exact (eq_refl (term104 p)). Qed.
Lemma lem212361 (m : nat) (p : nat) : ((term213 p m) = (term104 p)) = ((Peano.le p m) = (term104 p)).
Proof. exact (MK_COMB (@lem212359 p m) (@lem212360 p)). Qed.
Lemma lem212362 (m : nat) (p : nat) : ((term213 p m) = (term214 p)) = ((Peano.le p m) = (term104 p)).
Proof. exact (TRANS (@lem212356 m p) (@lem212361 m p)). Qed.
Lemma lem212363 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le p m) = (term104 p).
Proof. exact (EQ_MP (@lem212362 m p) (@lem212353 p m h1)). Qed.
Lemma lem212420 (_4246 : nat) (h1 : term108) : term152 _4246.
Proof. exact (EQ_MP (@lem212204 _4246) (@lem212203 _4246 h1)). Qed.
Lemma lem212545 (p : nat) (m : nat) (h1 : Peano.le p m) (h2 : m = (NUMERAL 0)) : term104 p.
Proof. exact (EQ_MP (@lem212363 p m h2) (@lem212237 p m h1)). Qed.
Lemma lem212546 (p : nat) (m : nat) (h1 : Peano.le p m) (h2 : m = (NUMERAL 0)) : term217 p.
Proof. exact (fun h0 : term218 p => @lem212545 p m h1 h2). Qed.
Lemma lem212548 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212549 (p : nat) : (term217 p) = (term104 p).
Proof. exact (@lem212548 (term104 p)). Qed.
Lemma lem212550 (p : nat) (m : nat) (h1 : Peano.le p m) (h2 : m = (NUMERAL 0)) : term104 p.
Proof. exact (EQ_MP (@lem212549 p) (@lem212546 p m h1 h2)). Qed.
Lemma lem212556 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem212557 (_4246 : nat) : (term152 _4246) = (term220 _4246).
Proof. exact (@lem212556 (_4246 = (NUMERAL 0)) (term218 _4246)). Qed.
Lemma lem212565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem212566 (_4246 : nat) : (term221 _4246) = (term222 _4246).
Proof. exact (MK_COMB (@lem212565) (@lem212557 _4246)). Qed.
Lemma lem212574 (_4246 : nat) : (term220 _4246) = (term220 _4246).
Proof. exact (eq_refl (term220 _4246)). Qed.
Lemma lem212575 (_4246 : nat) : ((term152 _4246) = (term220 _4246)) = ((term220 _4246) = (term220 _4246)).
Proof. exact (MK_COMB (@lem212566 _4246) (@lem212574 _4246)). Qed.
Lemma lem212577 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem212578 (x : Prop) : (x = x) = True.
Proof. exact (@lem212577 Prop x). Qed.
Lemma lem212579 (_4246 : nat) : ((term220 _4246) = (term220 _4246)) = True.
Proof. exact (@lem212578 (term220 _4246)). Qed.
Lemma lem212580 (_4246 : nat) : ((term152 _4246) = (term220 _4246)) = True.
Proof. exact (TRANS (@lem212575 _4246) (@lem212579 _4246)). Qed.
Lemma lem212581 (_4246 : nat) : True = ((term152 _4246) = (term220 _4246)).
Proof. exact (SYM (@lem212580 _4246)). Qed.
Lemma lem212582 (_4246 : nat) : (term152 _4246) = (term220 _4246).
Proof. exact (EQ_MP (@lem212581 _4246) (@lem0)). Qed.
Lemma lem212583 (_4246 : nat) (h1 : term108) : term220 _4246.
Proof. exact (EQ_MP (@lem212582 _4246) (@lem212420 _4246 h1)). Qed.
Lemma lem212585 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem212586 (_4246 : nat) : (term220 _4246) = (term224 _4246).
Proof. exact (@lem212585 (term218 _4246) (_4246 = (NUMERAL 0))). Qed.
Lemma lem212588 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem212589 (_4246 : nat) : (term226 _4246) = (term104 _4246).
Proof. exact (@lem212588 (term104 _4246)). Qed.
Lemma lem212590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem212591 (_4246 : nat) : (term227 _4246) = (term228 _4246).
Proof. exact (MK_COMB (@lem212590) (@lem212589 _4246)). Qed.
Lemma lem212592 (_4246 : nat) : (_4246 = (NUMERAL 0)) = (_4246 = (NUMERAL 0)).
Proof. exact (eq_refl (_4246 = (NUMERAL 0))). Qed.
Lemma lem212593 (_4246 : nat) : (term224 _4246) = (term229 _4246).
Proof. exact (MK_COMB (@lem212591 _4246) (@lem212592 _4246)). Qed.
Lemma lem212594 (_4246 : nat) : (term220 _4246) = (term229 _4246).
Proof. exact (TRANS (@lem212586 _4246) (@lem212593 _4246)). Qed.
Lemma lem212597 (_4246 : nat) (h1 : term108) : term229 _4246.
Proof. exact (EQ_MP (@lem212594 _4246) (@lem212583 _4246 h1)). Qed.
Lemma lem212598 (p : nat) (h1 : term108) : term229 p.
Proof. exact (@lem212597 p h1). Qed.
Lemma lem212601 (p : nat) (m : nat) (h1 : term108) (h2 : Peano.le p m) (h3 : m = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (@lem212598 p h1 (@lem212550 p m h2 h3)). Qed.
Lemma lem212602 (p : nat) (m : nat) (h1 : term108) (h2 : Peano.le p m) (h3 : m = (NUMERAL 0)) : term230 p.
Proof. exact (fun h0 : term25 p => @lem212601 p m h1 h2 h3). Qed.
Lemma lem212604 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212605 (p : nat) : (term230 p) = (p = (NUMERAL 0)).
Proof. exact (@lem212604 (p = (NUMERAL 0))). Qed.
Lemma lem212606 (p : nat) (m : nat) (h1 : term108) (h2 : Peano.le p m) (h3 : m = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (EQ_MP (@lem212605 p) (@lem212602 p m h1 h2 h3)). Qed.
Lemma lem212609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem212611 (p : nat) : (term25 p) = (term231 p).
Proof. exact (@lem212609 (p = (NUMERAL 0))). Qed.
Lemma lem212614 (p : nat) (h1 : term25 p) : term231 p.
Proof. exact (EQ_MP (@lem212611 p) (@lem212351 p h1)). Qed.
Lemma lem212617 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (@lem212614 p h1 (@lem212606 p m h2 h3 h4)). Qed.
Lemma lem212618 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : term232.
Proof. exact (fun h0 : ~ False => @lem212617 p m h1 h2 h3 h4). Qed.
Lemma lem212620 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212621 : term232 = False.
Proof. exact (@lem212620 False). Qed.
Lemma lem212622 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem212621) (@lem212618 p m h1 h2 h3 h4)). Qed.
Lemma lem212642 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem212643 (_4299 : nat) (_4301 : nat) (h1 : _4299 = _4301) : _4299 = _4301.
Proof. exact (h1). Qed.
Lemma lem212644 (_4300 : nat) (_4302 : nat) (h1 : _4300 = _4302) : _4300 = _4302.
Proof. exact (h1). Qed.
Lemma lem212645 (_4299 : nat) (_4301 : nat) (h1 : _4299 = _4301) : (Peano.le _4299) = (Peano.le _4301).
Proof. exact (MK_COMB (@lem212642) (@lem212643 _4299 _4301 h1)). Qed.
Lemma lem212646 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) (h1 : _4299 = _4301) (h2 : _4300 = _4302) : (Peano.le _4299 _4300) = (Peano.le _4301 _4302).
Proof. exact (MK_COMB (@lem212645 _4299 _4301 h1) (@lem212644 _4300 _4302 h2)). Qed.
Lemma lem212648 (b : Prop) (a : Prop) : term233 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem212649 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : term234 _4301 _4302 _4299 _4300.
Proof. exact (@lem212648 (Peano.le _4301 _4302) (Peano.le _4299 _4300)). Qed.
Lemma lem212650 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) (h1 : _4299 = _4301) (h2 : _4300 = _4302) : term235 _4301 _4302 _4299 _4300.
Proof. exact (@lem212649 _4301 _4302 _4299 _4300 (@lem212646 _4299 _4301 _4300 _4302 h1 h2)). Qed.
Lemma lem212651 (_4302 : nat) (_4300 : nat) (_4299 : nat) (_4301 : nat) (h1 : _4299 = _4301) : term236 _4301 _4302 _4299 _4300.
Proof. exact (fun h0 : _4300 = _4302 => @lem212650 _4299 _4301 _4300 _4302 h1 h0). Qed.
Lemma lem212653 (a : Prop) (b : Prop) : (a -> b) = (term237 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem212654 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term236 _4301 _4302 _4299 _4300) = (term238 _4301 _4302 _4299 _4300).
Proof. exact (@lem212653 (_4300 = _4302) (term235 _4301 _4302 _4299 _4300)). Qed.
Lemma lem212655 (_4302 : nat) (_4300 : nat) (_4299 : nat) (_4301 : nat) (h1 : _4299 = _4301) : term238 _4301 _4302 _4299 _4300.
Proof. exact (EQ_MP (@lem212654 _4301 _4302 _4299 _4300) (@lem212651 _4302 _4300 _4299 _4301 h1)). Qed.
Lemma lem212656 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : term239 _4301 _4302 _4299 _4300.
Proof. exact (fun h0 : _4299 = _4301 => @lem212655 _4302 _4300 _4299 _4301 h0). Qed.
Lemma lem212658 (a : Prop) (b : Prop) : (a -> b) = (term237 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem212659 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term239 _4301 _4302 _4299 _4300) = (term240 _4301 _4302 _4299 _4300).
Proof. exact (@lem212658 (_4299 = _4301) (term238 _4301 _4302 _4299 _4300)). Qed.
Lemma lem212660 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : term240 _4301 _4302 _4299 _4300.
Proof. exact (EQ_MP (@lem212659 _4301 _4302 _4299 _4300) (@lem212656 _4301 _4302 _4299 _4300)). Qed.
Lemma lem212738 (x : nat) (y : nat) (z : nat) : term241 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem212740 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem212741 (n : nat) (m : nat) : (term56 n m) = (term56 n m).
Proof. exact (@lem212740 (term56 n m)). Qed.
Lemma lem212742 (n : nat) (m : nat) : term242 n m.
Proof. exact (fun h0 : term243 n m => @lem212741 n m). Qed.
Lemma lem212744 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212745 (n : nat) (m : nat) : (term242 n m) = ((term56 n m) = (term56 n m)).
Proof. exact (@lem212744 ((term56 n m) = (term56 n m))). Qed.
Lemma lem212746 (n : nat) (m : nat) : (term56 n m) = (term56 n m).
Proof. exact (EQ_MP (@lem212745 n m) (@lem212742 n m)). Qed.
Lemma lem212748 (n : nat) (m : nat) (h1 : term110 n m) : n = (term244 n m).
Proof. exact (proj1 (@lem211975 n m h1)). Qed.
Lemma lem212749 (n : nat) (m : nat) (h1 : term110 n m) : term245 n m.
Proof. exact (fun h0 : term246 n m => @lem212748 n m h1). Qed.
Lemma lem212751 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212752 (n : nat) (m : nat) : (term245 n m) = (n = (term244 n m)).
Proof. exact (@lem212751 (n = (term244 n m))). Qed.
Lemma lem212753 (n : nat) (m : nat) (h1 : term110 n m) : n = (term244 n m).
Proof. exact (EQ_MP (@lem212752 n m) (@lem212749 n m h1)). Qed.
Lemma lem212755 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem212756 (n : nat) : n = n.
Proof. exact (@lem212755 n). Qed.
Lemma lem212757 (n : nat) : term247 n.
Proof. exact (fun h0 : term248 n => @lem212756 n). Qed.
Lemma lem212759 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212760 (n : nat) : (term247 n) = (n = n).
Proof. exact (@lem212759 (n = n)). Qed.
Lemma lem212761 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem212760 n) (@lem212757 n)). Qed.
Lemma lem212779 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem212780 (y : nat) (x : nat) (z : nat) : (term249 x y z) = (term250 y x z).
Proof. exact (@lem212779 (y = z) (term251 x z)). Qed.
Lemma lem212790 (x : nat) (y : nat) : (term252 x y) = (term252 x y).
Proof. exact (eq_refl (term252 x y)). Qed.
Lemma lem212791 (y : nat) (x : nat) (z : nat) : (term241 x y z) = (term253 y x z).
Proof. exact (MK_COMB (@lem212790 x y) (@lem212780 y x z)). Qed.
Lemma lem212795 (q : Prop) (p : Prop) (r : Prop) : (term254 p q r) = (term254 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem212796 (y : nat) (x : nat) (z : nat) : (term253 y x z) = (term255 y x z).
Proof. exact (@lem212795 (y = z) (term251 x y) (term251 x z)). Qed.
Lemma lem212818 (y : nat) (x : nat) (z : nat) : (term241 x y z) = (term255 y x z).
Proof. exact (TRANS (@lem212791 y x z) (@lem212796 y x z)). Qed.
Lemma lem212819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem212820 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term257 y x z).
Proof. exact (MK_COMB (@lem212819) (@lem212818 y x z)). Qed.
Lemma lem212842 (y : nat) (x : nat) (z : nat) : (term255 y x z) = (term255 y x z).
Proof. exact (eq_refl (term255 y x z)). Qed.
Lemma lem212843 (y : nat) (x : nat) (z : nat) : ((term241 x y z) = (term255 y x z)) = ((term255 y x z) = (term255 y x z)).
Proof. exact (MK_COMB (@lem212820 y x z) (@lem212842 y x z)). Qed.
Lemma lem212845 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem212846 (x : Prop) : (x = x) = True.
Proof. exact (@lem212845 Prop x). Qed.
Lemma lem212847 (y : nat) (x : nat) (z : nat) : ((term255 y x z) = (term255 y x z)) = True.
Proof. exact (@lem212846 (term255 y x z)). Qed.
Lemma lem212848 (y : nat) (x : nat) (z : nat) : ((term241 x y z) = (term255 y x z)) = True.
Proof. exact (TRANS (@lem212843 y x z) (@lem212847 y x z)). Qed.
Lemma lem212849 (y : nat) (x : nat) (z : nat) : True = ((term241 x y z) = (term255 y x z)).
Proof. exact (SYM (@lem212848 y x z)). Qed.
Lemma lem212850 (y : nat) (x : nat) (z : nat) : (term241 x y z) = (term255 y x z).
Proof. exact (EQ_MP (@lem212849 y x z) (@lem0)). Qed.
Lemma lem212851 (y : nat) (x : nat) (z : nat) : term255 y x z.
Proof. exact (EQ_MP (@lem212850 y x z) (@lem212738 x y z)). Qed.
Lemma lem212853 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem212854 (x : nat) (y : nat) (z : nat) : (term255 y x z) = (term258 x y z).
Proof. exact (@lem212853 (term259 y x z) (y = z)). Qed.
Lemma lem212856 (a : Prop) (b : Prop) : (term260 a b) = (term261 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem212857 (y : nat) (x : nat) (z : nat) : (term262 y x z) = (term263 y x z).
Proof. exact (@lem212856 (term251 x y) (term251 x z)). Qed.
Lemma lem212859 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem212860 (x : nat) (y : nat) : (term264 x y) = (x = y).
Proof. exact (@lem212859 (x = y)). Qed.
Lemma lem212861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem212862 (x : nat) (y : nat) : (term265 x y) = (term266 x y).
Proof. exact (MK_COMB (@lem212861) (@lem212860 x y)). Qed.
Lemma lem212864 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem212865 (x : nat) (z : nat) : (term264 x z) = (x = z).
Proof. exact (@lem212864 (x = z)). Qed.
Lemma lem212866 (y : nat) (x : nat) (z : nat) : (term263 y x z) = (term267 y x z).
Proof. exact (MK_COMB (@lem212862 x y) (@lem212865 x z)). Qed.
Lemma lem212867 (y : nat) (x : nat) (z : nat) : (term262 y x z) = (term267 y x z).
Proof. exact (TRANS (@lem212857 y x z) (@lem212866 y x z)). Qed.
Lemma lem212868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem212869 (y : nat) (x : nat) (z : nat) : (term268 y x z) = (term269 y x z).
Proof. exact (MK_COMB (@lem212868) (@lem212867 y x z)). Qed.
Lemma lem212870 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem212871 (x : nat) (y : nat) (z : nat) : (term258 x y z) = (term270 x y z).
Proof. exact (MK_COMB (@lem212869 y x z) (@lem212870 y z)). Qed.
Lemma lem212872 (x : nat) (y : nat) (z : nat) : (term255 y x z) = (term270 x y z).
Proof. exact (TRANS (@lem212854 x y z) (@lem212871 x y z)). Qed.
Lemma lem212874 (n : nat) (m : nat) (h1 : term110 n m) : term271 m n.
Proof. exact (conj (@lem212753 n m h1) (@lem212761 n)). Qed.
Lemma lem212876 (x : nat) (y : nat) (z : nat) : term270 x y z.
Proof. exact (EQ_MP (@lem212872 x y z) (@lem212851 y x z)). Qed.
Lemma lem212877 (m : nat) (n : nat) : term272 m n.
Proof. exact (@lem212876 n (term244 n m) n). Qed.
Lemma lem212880 (n : nat) (m : nat) (h1 : term110 n m) : (term244 n m) = n.
Proof. exact (@lem212877 m n (@lem212874 n m h1)). Qed.
Lemma lem212881 (n : nat) (m : nat) (h1 : term110 n m) : term273 m n.
Proof. exact (fun h0 : term274 m n => @lem212880 n m h1). Qed.
Lemma lem212883 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212884 (m : nat) (n : nat) : (term273 m n) = ((term244 n m) = n).
Proof. exact (@lem212883 ((term244 n m) = n)). Qed.
Lemma lem212885 (n : nat) (m : nat) (h1 : term110 n m) : (term244 n m) = n.
Proof. exact (EQ_MP (@lem212884 m n) (@lem212881 n m h1)). Qed.
Lemma lem212887 (_4247 : nat) (_4248 : nat) (h1 : term70) : term94 _4247 _4248.
Proof. exact (EQ_MP (@lem212210 _4247 _4248) (@lem212209 _4247 _4248 h1)). Qed.
Lemma lem212888 (n : nat) (m : nat) (h1 : term70) : term275 n m.
Proof. exact (@lem212887 (term56 n m) (Nat.modulo n m) h1). Qed.
Lemma lem212889 (n : nat) (m : nat) (h1 : term70) : term276 n m.
Proof. exact (fun h0 : term277 n m => @lem212888 n m h1). Qed.
Lemma lem212891 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem212892 (n : nat) (m : nat) : (term276 n m) = (term275 n m).
Proof. exact (@lem212891 (term275 n m)). Qed.
Lemma lem212893 (n : nat) (m : nat) (h1 : term70) : term275 n m.
Proof. exact (EQ_MP (@lem212892 n m) (@lem212889 n m h1)). Qed.
Lemma lem212911 (q : Prop) (p : Prop) (r : Prop) : (term254 p q r) = (term254 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem212912 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term238 _4301 _4302 _4299 _4300) = (term278 _4301 _4302 _4299 _4300).
Proof. exact (@lem212911 (Peano.le _4301 _4302) (term251 _4300 _4302) (term279 _4299 _4300)). Qed.
Lemma lem212926 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem212927 (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term280 _4302 _4299 _4300) = (term281 _4299 _4300 _4302).
Proof. exact (@lem212926 (term279 _4299 _4300) (term251 _4300 _4302)). Qed.
Lemma lem212935 (_4301 : nat) (_4302 : nat) : (term49 _4301 _4302) = (term49 _4301 _4302).
Proof. exact (eq_refl (term49 _4301 _4302)). Qed.
Lemma lem212936 (_4301 : nat) (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term278 _4301 _4302 _4299 _4300) = (term282 _4301 _4299 _4300 _4302).
Proof. exact (MK_COMB (@lem212935 _4301 _4302) (@lem212927 _4299 _4300 _4302)). Qed.
Lemma lem212947 (_4301 : nat) (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term238 _4301 _4302 _4299 _4300) = (term282 _4301 _4299 _4300 _4302).
Proof. exact (TRANS (@lem212912 _4301 _4302 _4299 _4300) (@lem212936 _4301 _4299 _4300 _4302)). Qed.
Lemma lem212948 (_4299 : nat) (_4301 : nat) : (term252 _4299 _4301) = (term252 _4299 _4301).
Proof. exact (eq_refl (term252 _4299 _4301)). Qed.
Lemma lem212949 (_4301 : nat) (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term240 _4301 _4302 _4299 _4300) = (term283 _4301 _4299 _4300 _4302).
Proof. exact (MK_COMB (@lem212948 _4299 _4301) (@lem212947 _4301 _4299 _4300 _4302)). Qed.
Lemma lem212953 (q : Prop) (p : Prop) (r : Prop) : (term254 p q r) = (term254 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem212954 (_4301 : nat) (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term283 _4301 _4299 _4300 _4302) = (term284 _4301 _4299 _4300 _4302).
Proof. exact (@lem212953 (Peano.le _4301 _4302) (term251 _4299 _4301) (term281 _4299 _4300 _4302)). Qed.
Lemma lem212968 (q : Prop) (p : Prop) (r : Prop) : (term254 p q r) = (term254 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem212969 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term285 _4301 _4299 _4300 _4302) = (term286 _4299 _4301 _4300 _4302).
Proof. exact (@lem212968 (term279 _4299 _4300) (term251 _4299 _4301) (term251 _4300 _4302)). Qed.
Lemma lem212989 (_4301 : nat) (_4302 : nat) : (term49 _4301 _4302) = (term49 _4301 _4302).
Proof. exact (eq_refl (term49 _4301 _4302)). Qed.
Lemma lem212990 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term284 _4301 _4299 _4300 _4302) = (term287 _4299 _4301 _4300 _4302).
Proof. exact (MK_COMB (@lem212989 _4301 _4302) (@lem212969 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213001 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term283 _4301 _4299 _4300 _4302) = (term287 _4299 _4301 _4300 _4302).
Proof. exact (TRANS (@lem212954 _4301 _4299 _4300 _4302) (@lem212990 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213002 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term240 _4301 _4302 _4299 _4300) = (term287 _4299 _4301 _4300 _4302).
Proof. exact (TRANS (@lem212949 _4301 _4299 _4300 _4302) (@lem213001 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem213004 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term288 _4301 _4302 _4299 _4300) = (term289 _4299 _4301 _4300 _4302).
Proof. exact (MK_COMB (@lem213003) (@lem213002 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213030 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem213031 (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term280 _4302 _4299 _4300) = (term281 _4299 _4300 _4302).
Proof. exact (@lem213030 (term279 _4299 _4300) (term251 _4300 _4302)). Qed.
Lemma lem213039 (_4299 : nat) (_4301 : nat) : (term252 _4299 _4301) = (term252 _4299 _4301).
Proof. exact (eq_refl (term252 _4299 _4301)). Qed.
Lemma lem213040 (_4301 : nat) (_4299 : nat) (_4300 : nat) (_4302 : nat) : (term290 _4301 _4302 _4299 _4300) = (term285 _4301 _4299 _4300 _4302).
Proof. exact (MK_COMB (@lem213039 _4299 _4301) (@lem213031 _4299 _4300 _4302)). Qed.
Lemma lem213044 (q : Prop) (p : Prop) (r : Prop) : (term254 p q r) = (term254 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem213045 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term285 _4301 _4299 _4300 _4302) = (term286 _4299 _4301 _4300 _4302).
Proof. exact (@lem213044 (term279 _4299 _4300) (term251 _4299 _4301) (term251 _4300 _4302)). Qed.
Lemma lem213065 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term290 _4301 _4302 _4299 _4300) = (term286 _4299 _4301 _4300 _4302).
Proof. exact (TRANS (@lem213040 _4301 _4299 _4300 _4302) (@lem213045 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213066 (_4301 : nat) (_4302 : nat) : (term49 _4301 _4302) = (term49 _4301 _4302).
Proof. exact (eq_refl (term49 _4301 _4302)). Qed.
Lemma lem213067 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : (term291 _4301 _4302 _4299 _4300) = (term287 _4299 _4301 _4300 _4302).
Proof. exact (MK_COMB (@lem213066 _4301 _4302) (@lem213065 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213078 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : ((term240 _4301 _4302 _4299 _4300) = (term291 _4301 _4302 _4299 _4300)) = ((term287 _4299 _4301 _4300 _4302) = (term287 _4299 _4301 _4300 _4302)).
Proof. exact (MK_COMB (@lem213004 _4299 _4301 _4300 _4302) (@lem213067 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem213081 (x : Prop) : (x = x) = True.
Proof. exact (@lem213080 Prop x). Qed.
Lemma lem213082 (_4299 : nat) (_4301 : nat) (_4300 : nat) (_4302 : nat) : ((term287 _4299 _4301 _4300 _4302) = (term287 _4299 _4301 _4300 _4302)) = True.
Proof. exact (@lem213081 (term287 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213083 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : ((term240 _4301 _4302 _4299 _4300) = (term291 _4301 _4302 _4299 _4300)) = True.
Proof. exact (TRANS (@lem213078 _4299 _4301 _4300 _4302) (@lem213082 _4299 _4301 _4300 _4302)). Qed.
Lemma lem213084 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : True = ((term240 _4301 _4302 _4299 _4300) = (term291 _4301 _4302 _4299 _4300)).
Proof. exact (SYM (@lem213083 _4301 _4302 _4299 _4300)). Qed.
Lemma lem213085 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term240 _4301 _4302 _4299 _4300) = (term291 _4301 _4302 _4299 _4300).
Proof. exact (EQ_MP (@lem213084 _4301 _4302 _4299 _4300) (@lem0)). Qed.
Lemma lem213086 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : term291 _4301 _4302 _4299 _4300.
Proof. exact (EQ_MP (@lem213085 _4301 _4302 _4299 _4300) (@lem212660 _4301 _4302 _4299 _4300)). Qed.
Lemma lem213088 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem213089 (_4299 : nat) (_4300 : nat) (_4301 : nat) (_4302 : nat) : (term291 _4301 _4302 _4299 _4300) = (term292 _4299 _4300 _4301 _4302).
Proof. exact (@lem213088 (term290 _4301 _4302 _4299 _4300) (Peano.le _4301 _4302)). Qed.
Lemma lem213091 (a : Prop) (b : Prop) : (term260 a b) = (term261 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem213092 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term293 _4301 _4302 _4299 _4300) = (term294 _4301 _4302 _4299 _4300).
Proof. exact (@lem213091 (term251 _4299 _4301) (term280 _4302 _4299 _4300)). Qed.
Lemma lem213094 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem213095 (_4299 : nat) (_4301 : nat) : (term264 _4299 _4301) = (_4299 = _4301).
Proof. exact (@lem213094 (_4299 = _4301)). Qed.
Lemma lem213096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213097 (_4299 : nat) (_4301 : nat) : (term265 _4299 _4301) = (term266 _4299 _4301).
Proof. exact (MK_COMB (@lem213096) (@lem213095 _4299 _4301)). Qed.
Lemma lem213099 (a : Prop) (b : Prop) : (term260 a b) = (term261 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem213100 (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term295 _4302 _4299 _4300) = (term296 _4302 _4299 _4300).
Proof. exact (@lem213099 (term251 _4300 _4302) (term279 _4299 _4300)). Qed.
Lemma lem213102 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem213103 (_4300 : nat) (_4302 : nat) : (term264 _4300 _4302) = (_4300 = _4302).
Proof. exact (@lem213102 (_4300 = _4302)). Qed.
Lemma lem213104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213105 (_4300 : nat) (_4302 : nat) : (term265 _4300 _4302) = (term266 _4300 _4302).
Proof. exact (MK_COMB (@lem213104) (@lem213103 _4300 _4302)). Qed.
Lemma lem213107 (a : Prop) : (term225 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem213108 (_4299 : nat) (_4300 : nat) : (term297 _4299 _4300) = (Peano.le _4299 _4300).
Proof. exact (@lem213107 (Peano.le _4299 _4300)). Qed.
Lemma lem213109 (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term296 _4302 _4299 _4300) = (term298 _4302 _4299 _4300).
Proof. exact (MK_COMB (@lem213105 _4300 _4302) (@lem213108 _4299 _4300)). Qed.
Lemma lem213110 (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term295 _4302 _4299 _4300) = (term298 _4302 _4299 _4300).
Proof. exact (TRANS (@lem213100 _4302 _4299 _4300) (@lem213109 _4302 _4299 _4300)). Qed.
Lemma lem213111 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term294 _4301 _4302 _4299 _4300) = (term299 _4301 _4302 _4299 _4300).
Proof. exact (MK_COMB (@lem213097 _4299 _4301) (@lem213110 _4302 _4299 _4300)). Qed.
Lemma lem213112 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term293 _4301 _4302 _4299 _4300) = (term299 _4301 _4302 _4299 _4300).
Proof. exact (TRANS (@lem213092 _4301 _4302 _4299 _4300) (@lem213111 _4301 _4302 _4299 _4300)). Qed.
Lemma lem213113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem213114 (_4301 : nat) (_4302 : nat) (_4299 : nat) (_4300 : nat) : (term300 _4301 _4302 _4299 _4300) = (term301 _4301 _4302 _4299 _4300).
Proof. exact (MK_COMB (@lem213113) (@lem213112 _4301 _4302 _4299 _4300)). Qed.
Lemma lem213115 (_4301 : nat) (_4302 : nat) : (Peano.le _4301 _4302) = (Peano.le _4301 _4302).
Proof. exact (eq_refl (Peano.le _4301 _4302)). Qed.
Lemma lem213116 (_4299 : nat) (_4300 : nat) (_4301 : nat) (_4302 : nat) : (term292 _4299 _4300 _4301 _4302) = (term302 _4299 _4300 _4301 _4302).
Proof. exact (MK_COMB (@lem213114 _4301 _4302 _4299 _4300) (@lem213115 _4301 _4302)). Qed.
Lemma lem213117 (_4299 : nat) (_4300 : nat) (_4301 : nat) (_4302 : nat) : (term291 _4301 _4302 _4299 _4300) = (term302 _4299 _4300 _4301 _4302).
Proof. exact (TRANS (@lem213089 _4299 _4300 _4301 _4302) (@lem213116 _4299 _4300 _4301 _4302)). Qed.
Lemma lem213119 (n : nat) (m : nat) (h1 : term70) (h2 : term110 n m) : term303 n m.
Proof. exact (conj (@lem212885 n m h2) (@lem212893 n m h1)). Qed.
Lemma lem213120 (n : nat) (m : nat) (h1 : term70) (h2 : term110 n m) : term304 n m.
Proof. exact (conj (@lem212746 n m) (@lem213119 n m h1 h2)). Qed.
Lemma lem213122 (_4299 : nat) (_4300 : nat) (_4301 : nat) (_4302 : nat) : term302 _4299 _4300 _4301 _4302.
Proof. exact (EQ_MP (@lem213117 _4299 _4300 _4301 _4302) (@lem213086 _4301 _4302 _4299 _4300)). Qed.
Lemma lem213123 (m : nat) (n : nat) : term305 m n.
Proof. exact (@lem213122 (term56 n m) (term244 n m) (term56 n m) n). Qed.
Lemma lem213126 (n : nat) (m : nat) (h1 : term70) (h2 : term110 n m) : term59 m n.
Proof. exact (@lem213123 m n (@lem213120 n m h1 h2)). Qed.
Lemma lem213127 (n : nat) (m : nat) (h1 : term70) (h2 : term110 n m) : term306 m n.
Proof. exact (fun h0 : term115 m n => @lem213126 n m h1 h2). Qed.
Lemma lem213129 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem213130 (m : nat) (n : nat) : (term306 m n) = (term59 m n).
Proof. exact (@lem213129 (term59 m n)). Qed.
Lemma lem213131 (n : nat) (m : nat) (h1 : term70) (h2 : term110 n m) : term59 m n.
Proof. exact (EQ_MP (@lem213130 m n) (@lem213127 n m h1 h2)). Qed.
Lemma lem213134 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem213136 (m : nat) (n : nat) : (term115 m n) = (term307 m n).
Proof. exact (@lem213134 (term59 m n)). Qed.
Lemma lem213139 (m : nat) (n : nat) (h1 : term63 m n) : term307 m n.
Proof. exact (EQ_MP (@lem213136 m n) (@lem212307 m n h1)). Qed.
Lemma lem213142 (n : nat) (m : nat) (h1 : term70) (h2 : term63 m n) (h3 : term110 n m) : False.
Proof. exact (@lem213139 m n h2 (@lem213131 n m h1 h3)). Qed.
Lemma lem213143 (n : nat) (m : nat) (h1 : term70) (h2 : term63 m n) (h3 : term110 n m) : term232.
Proof. exact (fun h0 : ~ False => @lem213142 n m h1 h2 h3). Qed.
Lemma lem213145 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem213146 : term232 = False.
Proof. exact (@lem213145 False). Qed.
Lemma lem213147 (n : nat) (m : nat) (h1 : term70) (h2 : term63 m n) (h3 : term110 n m) : False.
Proof. exact (EQ_MP (@lem213146) (@lem213143 n m h1 h2 h3)). Qed.
Lemma lem213148 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (term25 p) = False.
Proof. exact (prop_ext (fun h5 : term25 p => @lem212622 p m h1 h2 h3 h4) (fun h5 : False => @lem212351 p h1)). Qed.
Lemma lem213150 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213148 p m h1 h2 h3 h4) (@lem212351 p h1)). Qed.
Lemma lem213151 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem213150 p m h1 h2 h3 h4) (fun h5 : False => @lem212265 m h4)). Qed.
Lemma lem213152 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213151 p m h1 h2 h3 h4) (@lem212265 m h4)). Qed.
Lemma lem213153 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (Peano.le p m) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p m => @lem213152 p m h1 h2 h3 h4) (fun h5 : False => @lem212237 p m h3)). Qed.
Lemma lem213154 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213153 p m h1 h2 h3 h4) (@lem212237 p m h3)). Qed.
Lemma lem213155 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (term25 p) = False.
Proof. exact (prop_ext (fun h5 : term25 p => @lem213154 p m h1 h2 h3 h4) (fun h5 : False => @lem212235 p h1)). Qed.
Lemma lem213156 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213155 p m h1 h2 h3 h4) (@lem212235 p h1)). Qed.
Lemma lem213157 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem213156 p m h1 h2 h3 h4) (fun h5 : False => @lem212077 m h4)). Qed.
Lemma lem213158 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213157 p m h1 h2 h3 h4) (@lem212077 m h4)). Qed.
Lemma lem213159 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (Peano.le p m) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p m => @lem213158 p m h1 h2 h3 h4) (fun h5 : False => @lem211985 p m h3)). Qed.
Lemma lem213160 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213159 p m h1 h2 h3 h4) (@lem211985 p m h3)). Qed.
Lemma lem213161 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (term25 p) = False.
Proof. exact (prop_ext (fun h5 : term25 p => @lem213160 p m h1 h2 h3 h4) (fun h5 : False => @lem211981 p h1)). Qed.
Lemma lem213162 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213161 p m h1 h2 h3 h4) (@lem211981 p h1)). Qed.
Lemma lem213163 (n : nat) (m : nat) (h1 : term70) (h2 : term63 m n) (h3 : term110 n m) : term70 = False.
Proof. exact (prop_ext (fun h4 : term70 => @lem213147 n m h1 h2 h3) (fun h4 : False => @lem212095 h1)). Qed.
Lemma lem213164 (n : nat) (m : nat) (h1 : term70) (h2 : term63 m n) (h3 : term110 n m) : False.
Proof. exact (EQ_MP (@lem213163 n m h1 h2 h3) (@lem212095 h1)). Qed.
Lemma lem213165 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : m = (NUMERAL 0) => @lem213162 p m h1 h2 h3 h4) (fun h5 : False => @lem212077 m h4)). Qed.
Lemma lem213166 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213165 p m h1 h2 h3 h4) (@lem212077 m h4)). Qed.
Lemma lem213167 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (Peano.le p m) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p m => @lem213166 p m h1 h2 h3 h4) (fun h5 : False => @lem211985 p m h3)). Qed.
Lemma lem213168 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213167 p m h1 h2 h3 h4) (@lem211985 p m h3)). Qed.
Lemma lem213169 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : (term25 p) = False.
Proof. exact (prop_ext (fun h5 : term25 p => @lem213168 p m h1 h2 h3 h4) (fun h5 : False => @lem211981 p h1)). Qed.
Lemma lem213170 (p : nat) (m : nat) (h1 : term25 p) (h2 : term108) (h3 : Peano.le p m) (h4 : m = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem213169 p m h1 h2 h3 h4) (@lem211981 p h1)). Qed.
Lemma lem213171 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (or_elim (@lem211973 m n h3) (fun h0 : m = (NUMERAL 0) => @lem213170 p m h2 h4 h5 h0) (fun h0 : term110 n m => @lem213164 n m h1 h3 h0)). Qed.
Lemma lem213172 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : term70 = False.
Proof. exact (prop_ext (fun h6 : term70 => @lem213171 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211965 h1)). Qed.
Lemma lem213173 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213172 n p m h1 h2 h3 h4 h5) (@lem211965 h1)). Qed.
Lemma lem213174 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : (Peano.le p m) = False.
Proof. exact (prop_ext (fun h6 : Peano.le p m => @lem213173 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211765 p m h5)). Qed.
Lemma lem213175 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213174 n p m h1 h2 h3 h4 h5) (@lem211765 p m h5)). Qed.
Lemma lem213176 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : (term25 p) = False.
Proof. exact (prop_ext (fun h6 : term25 p => @lem213175 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211759 p h2)). Qed.
Lemma lem213177 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213176 n p m h1 h2 h3 h4 h5) (@lem211759 p h2)). Qed.
Lemma lem213178 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : term70 = False.
Proof. exact (prop_ext (fun h6 : term70 => @lem213177 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211749 h1)). Qed.
Lemma lem213179 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213178 n p m h1 h2 h3 h4 h5) (@lem211749 h1)). Qed.
Lemma lem213180 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : (Peano.le p m) = False.
Proof. exact (prop_ext (fun h6 : Peano.le p m => @lem213179 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211261 p m h5)). Qed.
Lemma lem213181 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213180 n p m h1 h2 h3 h4 h5) (@lem211261 p m h5)). Qed.
Lemma lem213182 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : (term25 p) = False.
Proof. exact (prop_ext (fun h6 : term25 p => @lem213181 n p m h1 h2 h3 h4 h5) (fun h6 : False => @lem211255 p h2)). Qed.
Lemma lem213183 (n : nat) (p : nat) (m : nat) (h1 : term70) (h2 : term25 p) (h3 : term63 m n) (h4 : term108) (h5 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213182 n p m h1 h2 h3 h4 h5) (@lem211255 p h2)). Qed.
Lemma lem213184 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : term108) (h4 : Peano.le p m) : term68.
Proof. exact (fun h0 : term70 => @lem213183 n p m h0 h1 h2 h3 h4). Qed.
Lemma lem213185 : term68 = term69.
Proof. exact (@lem69 term70). Qed.
Lemma lem213186 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : term108) (h4 : Peano.le p m) : term69.
Proof. exact (EQ_MP (@lem213185) (@lem213184 n p m h1 h2 h3 h4)). Qed.
Lemma lem213187 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : term73.
Proof. exact (fun h0 : term108 => @lem213186 n p m h1 h2 h0 h3). Qed.
Lemma lem213188 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term76 m n.
Proof. exact (fun h0 : term63 m n => @lem213187 n p m h1 h0 h2). Qed.
Lemma lem213189 (m : nat) (n : nat) (p : nat) (h1 : term25 p) : term79 p m n.
Proof. exact (fun h0 : Peano.le p m => @lem213188 n p m h1 h0). Qed.
Lemma lem213190 (p : nat) (m : nat) (n : nat) : term81 p m n.
Proof. exact (fun h0 : term25 p => @lem213189 m n p h0). Qed.
Lemma lem213195 (m : nat) (n : nat) : term85 m n.
Proof. exact (fun p : nat => @lem213190 p m n). Qed.
Lemma lem213200 (n : nat) : term89 n.
Proof. exact (fun m : nat => @lem213195 m n). Qed.
Lemma lem213205 : term93.
Proof. exact (fun n : nat => @lem213200 n). Qed.
Lemma lem213206 : term92.
Proof. exact (EQ_MP (@lem211244) (@lem213205)). Qed.
Lemma lem213207 (n : nat) : term308 n.
Proof. exact (@lem213206 n). Qed.
Lemma lem213208 (n : nat) : (term308 n) = (term88 n).
Proof. exact (eq_refl (term308 n)). Qed.
Lemma lem213209 (n : nat) : term88 n.
Proof. exact (EQ_MP (@lem213208 n) (@lem213207 n)). Qed.
Lemma lem213210 (n : nat) (m : nat) : term309 n m.
Proof. exact (@lem213209 n m). Qed.
Lemma lem213211 (m : nat) (n : nat) : (term309 n m) = (term84 m n).
Proof. exact (eq_refl (term309 n m)). Qed.
Lemma lem213212 (m : nat) (n : nat) : term84 m n.
Proof. exact (EQ_MP (@lem213211 m n) (@lem213210 n m)). Qed.
Lemma lem213213 (m : nat) (n : nat) (p : nat) : term310 m n p.
Proof. exact (@lem213212 m n p). Qed.
Lemma lem213214 (p : nat) (m : nat) (n : nat) : (term310 m n p) = (term64 p m n).
Proof. exact (eq_refl (term310 m n p)). Qed.
Lemma lem213215 (p : nat) (m : nat) (n : nat) : term64 p m n.
Proof. exact (EQ_MP (@lem213214 p m n) (@lem213213 m n p)). Qed.
Lemma lem213217 (p : nat) (m : nat) (n : nat) : term64 p m n.
Proof. exact (@lem211003 p m n (@lem213215 p m n)). Qed.
Lemma lem213218 (m : nat) (n : nat) (p : nat) (h1 : term25 p) : term78 p m n.
Proof. exact (@lem213217 p m n (@lem210874 p h1)). Qed.
Lemma lem213219 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term75 m n.
Proof. exact (@lem213218 m n p h1 (@lem210873 p m h2)). Qed.
Lemma lem213220 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : term72.
Proof. exact (@lem213219 n p m h1 h3 (@lem210988 m n h2)). Qed.
Lemma lem213221 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : term68.
Proof. exact (@lem213220 n p m h1 h2 h3 (@lem89501)). Qed.
Lemma lem213222 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : False.
Proof. exact (@lem213221 n p m h1 h2 h3 (@lem100517)). Qed.
Lemma lem213223 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : (term63 m n) = False.
Proof. exact (prop_ext (fun h4 : term63 m n => @lem213222 n p m h1 h2 h3) (fun h4 : False => @lem210988 m n h2)). Qed.
Lemma lem213224 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term63 m n) (h3 : Peano.le p m) : False.
Proof. exact (EQ_MP (@lem213223 n p m h1 h2 h3) (@lem210988 m n h2)). Qed.
Lemma lem213225 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term62 m n.
Proof. exact (fun h0 : term63 m n => @lem213224 n p m h1 h0 h2). Qed.
Lemma lem213226 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term61 m n.
Proof. exact (EQ_MP (@lem210987 m n) (@lem213225 n p m h1 h2)). Qed.
Lemma lem213227 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term59 m n.
Proof. exact (@lem213226 n p m h1 h2 (@lem210837 n m)). Qed.
Lemma lem213228 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term52 m n.
Proof. exact (EQ_MP (@lem210983 m n) (@lem213227 n p m h1 h2)). Qed.
Lemma lem213229 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term53 p m n.
Proof. exact (EQ_MP (@lem210975 n p m h2) (@lem213228 n p m h1 h2)). Qed.
Lemma lem213230 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term311 p m n.
Proof. exact (ex_intro (term312 p m n) (term55 n m) (@lem213229 n p m h1 h2)). Qed.
Lemma lem213231 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term37 p m n.
Proof. exact (@lem210922 p m n (@lem213230 n p m h1 h2)). Qed.
Lemma lem213232 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term36 m n p.
Proof. exact (EQ_MP (@lem210919 m n p h1) (@lem213231 n p m h1 h2)). Qed.
Lemma lem213233 (p : nat) (m : nat) (h1 : term24 p m) : Peano.le p m.
Proof. exact (proj2 (@lem210872 p m h1)). Qed.
Lemma lem213234 (p : nat) (m : nat) (h1 : term24 p m) : term25 p.
Proof. exact (proj1 (@lem210872 p m h1)). Qed.
Lemma lem213235 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : (Peano.le p m) = (term36 m n p).
Proof. exact (prop_ext (fun h3 : Peano.le p m => @lem213232 n p m h1 h2) (fun h3 : term36 m n p => @lem210873 p m h2)). Qed.
Lemma lem213236 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term36 m n p.
Proof. exact (EQ_MP (@lem213235 n p m h1 h2) (@lem210873 p m h2)). Qed.
Lemma lem213237 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : (term25 p) = (term36 m n p).
Proof. exact (prop_ext (fun h3 : term25 p => @lem213236 n p m h1 h2) (fun h3 : term36 m n p => @lem210874 p h1)). Qed.
Lemma lem213238 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : Peano.le p m) : term36 m n p.
Proof. exact (EQ_MP (@lem213237 n p m h1 h2) (@lem210874 p h1)). Qed.
Lemma lem213239 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term24 p m) : (Peano.le p m) = (term36 m n p).
Proof. exact (prop_ext (fun h3 : Peano.le p m => @lem213238 n p m h1 h3) (fun h3 : term36 m n p => @lem213233 p m h2)). Qed.
Lemma lem213240 (n : nat) (p : nat) (m : nat) (h1 : term25 p) (h2 : term24 p m) : term36 m n p.
Proof. exact (EQ_MP (@lem213239 n p m h1 h2) (@lem213233 p m h2)). Qed.
Lemma lem213241 (n : nat) (p : nat) (m : nat) (h1 : term24 p m) : (term25 p) = (term36 m n p).
Proof. exact (prop_ext (fun h2 : term25 p => @lem213240 n p m h2 h1) (fun h2 : term36 m n p => @lem213234 p m h1)). Qed.
Lemma lem213242 (n : nat) (p : nat) (m : nat) (h1 : term24 p m) : term36 m n p.
Proof. exact (EQ_MP (@lem213241 n p m h1) (@lem213234 p m h1)). Qed.
Lemma lem213243 (m : nat) (n : nat) (p : nat) : term313 m n p.
Proof. exact (fun h0 : term24 p m => @lem213242 n p m h0). Qed.
Lemma lem213248 (m : nat) (n : nat) : term314 m n.
Proof. exact (fun p : nat => @lem213243 m n p). Qed.
Lemma lem213253 (m : nat) : term315 m.
Proof. exact (fun n : nat => @lem213248 m n). Qed.
Lemma lem213258 : term316.
Proof. exact (fun m : nat => @lem213253 m). Qed.
