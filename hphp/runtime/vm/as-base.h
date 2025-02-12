/*
   +----------------------------------------------------------------------+
   | HipHop for PHP                                                       |
   +----------------------------------------------------------------------+
   | Copyright (c) 2010-present Facebook, Inc. (http://www.facebook.com)  |
   +----------------------------------------------------------------------+
   | This source file is subject to version 3.01 of the PHP license,      |
   | that is bundled with this package in the file LICENSE, and is        |
   | available through the world-wide-web at the following url:           |
   | http://www.php.net/license/3_0p1.txt                                  |
   | If you did not receive a copy of the PHP license and are unable to   |
   | obtain it through the world-wide-web, please send a note to          |
   | license@php.net so we can mail you a copy immediately.               |
   +----------------------------------------------------------------------+
*/
#pragma once

#include <string>
#include <vector>

#include "hphp/runtime/base/attr.h"
#include "hphp/runtime/vm/fcall-args-flags.h"
#include "hphp/runtime/vm/type-constraint-flags.h"

namespace HPHP {

//////////////////////////////////////////////////////////////////////

/*
 * This header contains routines shared between HHVM and HackC.
 * Please be careful adding dependencies here. We need to avoid adding any
 * significant dependencies on HHVM from HackC.
 */

//////////////////////////////////////////////////////////////////////

/*
 * Attribute bits mean different things depending on context.  This
 * just enumerates the contexts the (dis)assembler cares about.
 */
enum class AttrContext {
  Class         = 0x1,
  Func          = 0x2,
  Prop          = 0x4,
  TraitImport   = 0x8,
  Alias         = 0x10,
  Parameter     = 0x20,
  Constant      = 0x40,
};

/*
 * Convert an attr to a vector of attribute names, for a given context.
 */
std::vector<std::string> attrs_to_vec(AttrContext, Attr);

/*
 * Convert an attr to a string of space-separated attribute names, for
 * a given context.
 */
std::string attrs_to_string(AttrContext, Attr);

/*
 * Convert TypeConstraint flags to a string of space-separated flag names.
 */
std::string type_flags_to_string(TypeConstraintFlags flags);

/*
 * Convert an fcall flag `to a string of space-separated flag names.
 */
std::string fcall_flags_to_string(FCallArgsFlags flags);
}
