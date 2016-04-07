//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
#ifndef _VCC_H
#define _VCC_H

#include <crtdefs.h>

#ifndef VERIFY

// hide annotations from C compiler

#define _(...) /* nothing */

#else

#include <vccp.h>

#endif

#endif // _VCC_H
