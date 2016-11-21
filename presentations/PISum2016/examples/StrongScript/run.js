if (typeof $$cts$$runtime === "undefined") {
    if (typeof require !== "undefined") require("./cts-runtime.js");
    else if (typeof document !== "undefined") { document.writeLine("<script src=\"cts-runtime.js\"></script>"); }
    else throw new Error("Could not load ConcreteTypeScript runtime!");
}
var Gun = (function () {
    function Gun() {
    }
    $$cts$$runtime.cement(Gun.prototype,"shoot",function () {
        $$cts$$runtime.cast(Gun,this);
        return this.$$cts$$value$shoot.apply(this, arguments);
    });
    $$cts$$runtime.cement(Gun.prototype,"$$cts$$value$shoot",function () {
    });
    return Gun;
})();
$$cts$$runtime.cementGlobal("Gun",Gun);
var Pencil = (function () {
    function Pencil() {
    }
    $$cts$$runtime.cement(Pencil.prototype,"write",function () {
        $$cts$$runtime.cast(Pencil,this);
        return this.$$cts$$value$write.apply(this, arguments);
    });
    $$cts$$runtime.cement(Pencil.prototype,"$$cts$$value$write",function () {
    });
    return Pencil;
})();
$$cts$$runtime.cementGlobal("Pencil",Pencil);
var Cowboy = (function () {
    function Cowboy() {
    }
    $$cts$$runtime.cement(Cowboy.prototype,"draw",function (gun) {
        $$cts$$runtime.cast(Cowboy,this);
        return this.$$cts$$value$draw.apply(this, arguments);
    });
    $$cts$$runtime.cement(Cowboy.prototype,"$$cts$$value$draw",function (gun) {
        gun.shoot();
    });
    $$cts$$runtime.cement(Cowboy.prototype,"draw2",function (gun) {
        $$cts$$runtime.cast(Cowboy,this);
        return this.$$cts$$value$draw2.apply(this, arguments);
    });
    $$cts$$runtime.cement(Cowboy.prototype,"$$cts$$value$draw2",function (gun) {
        gun.shoot();
    });
    $$cts$$runtime.cement(Cowboy.prototype,"draw3",function (gun) {
        $$cts$$runtime.cast(Cowboy,this);
        $$cts$$runtime.cast(Gun,gun);
        return this.$$cts$$value$draw3.apply(this, arguments);
    });
    $$cts$$runtime.cement(Cowboy.prototype,"$$cts$$value$draw3",function (gun) {
        gun.$$cts$$value$shoot();
    });
    return Cowboy;
})();
$$cts$$runtime.cementGlobal("Cowboy",Cowboy);
if (typeof $$cts$$runtime === "undefined") {
    if (typeof require !== "undefined") require("./cts-runtime.js");
    else if (typeof document !== "undefined") { document.writeLine("<script src=\"cts-runtime.js\"></script>"); }
    else throw new Error("Could not load ConcreteTypeScript runtime!");
}
new Cowboy().$$cts$$value$draw3(($$cts$$runtime.cast(Gun,(new Pencil()))));
