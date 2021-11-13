Require Import VST.floyd.proofauto.
Require Import seq_cmp.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.
(*Check Z.modulo.
Search Int.repr.
Print Int.modulus.
Print Int.max_signed.
Print Int.max_unsigned.*)

(*The comparison function*)
Definition compare (a b: Z) : Z :=
  if Z.eq_dec a b then 0%Z else 
  if Z_gt_le_dec a b then Z.modulo (a - b) Int.modulus (*TODO: see*) else
  Int.max_unsigned - (b - a - 1).
  (*Z.modulo (Int.max_unsigned - (b - a - 1)) Int.modulus.*)


Definition seq_cmp_spec :=
  DECLARE _seq_cmp
  WITH gv : globals, a : Z, b : Z
  PRE [tuint, tuint]
    PROP (0 <= a <= Int.max_unsigned; 0 <= b <= Int.max_unsigned)
    PARAMS(Vint (Int.repr a); Vint (Int.repr b))
    GLOBALS(gv)
    SEP ()
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (compare a b)))
    SEP ().

Definition Gprog := [seq_cmp_spec]. 

Lemma seq_cmp_spec_correct: semax_body Vprog Gprog f_seq_cmp seq_cmp_spec.
Proof.
  start_function. forward_if.
  - subst. forward. entailer!. unfold compare. destruct (Z.eq_dec b b); try lia. f_equal.
  - forward_if.
    + forward. unfold compare. destruct(Z.eq_dec); try lia. clear n.
      destruct (Z_gt_le_dec a b); try lia. clear g. entailer!. f_equal. apply modulo_samerepr.
      rewrite Zmod_mod. reflexivity.
    + forward. entailer!. unfold compare.  destruct(Z.eq_dec); try lia. clear n.
      destruct (Z_gt_le_dec a b); try lia. clear l. f_equal. unfold Int.max_unsigned.
      apply modulo_samerepr. rewrite <- (Z.sub_add_distr Int.modulus).
      rewrite <- (Zminus_mod_idemp_l Int.modulus). rewrite Z_mod_same_full. rewrite Z.sub_add_distr. reflexivity.
Qed.

(*Now we can prove the properties we want of this function *)

(*A more helpful Int.signed_repr_eq for our case:*)
Lemma Int_signed_repr_eq_sign: forall x,
  0 <= x <= Int.max_unsigned ->
  Int.signed (Int.repr x) > 0 <-> 0 < x < Int.half_modulus.
Proof.
  intros x Hx. rewrite Int.signed_repr_eq. assert (Hmod: x mod Int.modulus = x). { rewrite Zmod_small; rep_lia. }
  rewrite Hmod. destruct (zlt x Int.half_modulus); try rep_lia.
Qed.

(*Another, so we don't have do this manaually*)
Lemma Int_signed_repr_eq_sign_neg: forall x,
  0 <= x <= Int.max_unsigned ->
  Int.signed (Int.repr x) < 0 <-> x >= Int.half_modulus.
Proof.
  intros x Hx. rewrite Int.signed_repr_eq. assert (Hmod: x mod Int.modulus = x). { rewrite Zmod_small; rep_lia. }
  rewrite Hmod. destruct (zlt x Int.half_modulus); try rep_lia.
Qed.

(*From this, we can characterize the comparison: *)
Lemma compare_cases: forall a b,
  0 <= a <= Int.max_unsigned ->
  0 <= b <= Int.max_unsigned ->
  ((Int.signed (Int.repr (compare a b)) > 0) <-> 
   (b > a /\ b - a > Int.half_modulus) \/
   (a > b /\ a - b < Int.half_modulus)) /\
  ((Int.signed (Int.repr (compare a b)) < 0) <-> 
   (b > a /\ b - a <= Int.half_modulus) \/
   (a > b /\ a - b >= Int.half_modulus)) /\
  ((Int.signed (Int.repr (compare a b)) = 0) <-> a = b).
Proof.
  intros a b Ha Hb.
  assert (Hc: 0 <= compare a b <= Int.max_unsigned). { unfold compare.
    destruct (Z.eq_dec a b); try rep_lia. destruct (Z_gt_le_dec a b); try rep_lia.
    pose proof (Z_mod_lt (a-b) Int.modulus). rep_lia. }
  rewrite Int_signed_repr_eq_sign by auto. rewrite Int_signed_repr_eq_sign_neg by auto.
  unfold compare. destruct (Z.eq_dec a b); [repeat split; rep_lia |].
  destruct (Z_gt_le_dec a b).
  - assert (Hmod: (a - b) mod Int.modulus = (a-b)). { rewrite Zmod_small; rep_lia. }
    rewrite Hmod. split; try rep_lia. split; try rep_lia.
    split; try lia. rewrite Int.signed_repr_eq. rewrite Hmod.
    destruct (zlt (a - b) Int.half_modulus); rep_lia.
  - split; try rep_lia. split; try rep_lia.
    rewrite Int.signed_repr_eq.
    assert (Hmod: (Int.max_unsigned - (b - a - 1)) mod Int.modulus = (Int.modulus - (b - a))). {
      unfold Int.max_unsigned. rewrite Zmod_small; rep_lia. }
    rewrite Hmod. destruct (zlt (Int.modulus - (b - a)) Int.half_modulus); rep_lia.
Qed.

