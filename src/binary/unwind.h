#pragma once

#include "image.h"

namespace binary {
// Code that exception unwinders transfer control to without a direct branch: Windows funclets and
// continuations, and Itanium ABI landing pads. The translator lifts each so the runtime can resume it.

// Windows x64: catch funclets, continuations, and unwind actions named by __CxxFrameHandler3/4 data, and
// the filters, handlers, and targets of __C_specific_handler scope tables, for the .pdata table at `table`.
void windowsHandlerTargets(Bytes image, std::span<const GuestRegion> regions, std::size_t base, std::size_t table,
    std::size_t size, std::vector<LandingPad>& targets);

// MSVC C++ throw metadata: the destructors and copy constructors that ThrowInfo and CatchableType records
// name by RVA. The runtime calls them through pointers when it copies or destroys an exception object.
void windowsThrowTargets(Bytes image, std::span<const GuestRegion> regions, std::size_t base,
    std::vector<LandingPad>& targets);

// Landing pads named by the LSDAs of the .eh_frame entries at [frames, frames + size).
void frameLandingPads(Bytes image, std::size_t frames, std::size_t size, std::vector<LandingPad>& pads);

// Landing pads named by the LSDA index of a Mach-O __unwind_info section of the image whose header is at `header`.
void compactLandingPads(Bytes image, std::size_t header, std::size_t info, std::size_t size,
    std::vector<LandingPad>& pads);
}
