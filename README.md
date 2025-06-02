# smolnes-nut

The [smolnes](https://github.com/binji/smolnes) NES emulator, crudely ported to Squirrel for Portal 2.

Make sure to check out [binji](https://github.com/binji)'s amazing work on the original 5KB emulator.

## Usage
**Note: This section documents how to interface with the emulator as a Squirrel library. For a playable Portal 2 demo, see the next section.**

1. Include `smolnes.nut` in any script environment (or just copy its code into your source file). Note that it currently creates many globals with short and common names (e.g. `A`, `X`, `Y`, `val`, `result`, `dot`, etc.), which may not be suitable in some already populated environments.
2. Call `smolnes_init(rom)`, where `rom` is an array of 8-bit values representing the cartridge ROM buffer.
3. Define a global `smolnes_render` function to act as a render handler. This step is technically optional, but you likely want your emulator to actually render frames. This function won't be passed any arguments, as the actual framebuffer is stored in the `frame_buffer` global as a 1-dimensional 256x240 pixel BGR565 array.
4. Call `smolnes_loop()` to simulate a CPU cycle. In most Squirrel environments, this can be attached to a simple `while(true)` loop. For Source engine timeout workarounds, see the Portal 2 demo code.

## Example Demo

_TODO_
