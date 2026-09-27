# SPDX-FileCopyrightText: 2026 tao3k team and Contributors
#
# SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later

{
  pkgs,
  lib,
  config,
  inputs,
  ...
}:

{
  # https://devenv.sh/basics/
  env.GREET = "lean-poo";

  # https://devenv.sh/packages/
  packages = [
    pkgs.just
    pkgs.elan
  ];

  dotenv.enable = true;
  # https://devenv.sh/git-hooks/
  git-hooks.hooks = {
    shellcheck.enable = true;
    nixfmt.enable = true;
  };
  # See full reference at https://devenv.sh/reference/options/
}
