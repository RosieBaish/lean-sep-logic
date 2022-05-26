import Lake
open System Lake DSL

package sep_logic {
  dependencies := #[
    {
      name := `first_order_leaning
      src := Source.path (FilePath.mk ".." / "first_order_leaning")
    }
  ]
}
