'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

var React = require('react');

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

var React__default = /*#__PURE__*/_interopDefaultLegacy(React);

var defaultAvatars = {
  blue: 'https://cdn.discordapp.com/attachments/654503812593090602/665721745466195978/blue.png',
  gray: 'https://cdn.discordapp.com/attachments/654503812593090602/665721746569166849/gray.png',
  green: 'https://cdn.discordapp.com/attachments/654503812593090602/665721748431306753/green.png',
  orange: 'https://cdn.discordapp.com/attachments/654503812593090602/665721750201434138/orange.png',
  red: 'https://cdn.discordapp.com/attachments/654503812593090602/665721752277483540/red.png'
};
defaultAvatars["default"] = defaultAvatars.blue;
var DiscordDefaultOptions = {
  avatars: defaultAvatars,
  defaultMode: 'comfy',
  defaultTheme: 'dark',
  disableFont: true,
  profiles: {}
};

function createCommonjsModule(fn) {
  var module = { exports: {} };
	return fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret$1 = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret$1;

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has$1(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning$1(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning$1(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */







var has = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */



function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var propTypes = createCommonjsModule(function (module) {
if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

var elementsWithoutSlot = function elementsWithoutSlot(elements, name) {
  return React.Children.map(elements, function (element) {
    if (element.props && element.props.slot === name) return;
    return element;
  });
};
var findSlot = function findSlot(elements, name) {
  return React.Children.toArray(elements).find(function (_ref) {
    var _ref$props = _ref.props,
        props = _ref$props === void 0 ? {} : _ref$props;
    return props.slot && props.slot === name;
  });
};
var parseTimestamp = function parseTimestamp() {
  var timestamp = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : new Date();
  if (!(timestamp instanceof Date)) timestamp = new Date(timestamp);
  var _ref2 = [timestamp.getMonth() + 1, timestamp.getDate(), timestamp.getFullYear()],
      month = _ref2[0],
      day = _ref2[1],
      year = _ref2[2];
  return "".concat(month.toString().padStart(2, 0), "/").concat(day.toString().padStart(2, 0), "/").concat(year);
};

function styleInject(css, ref) {
  if ( ref === void 0 ) ref = {};
  var insertAt = ref.insertAt;

  if (!css || typeof document === 'undefined') { return; }

  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css$6 = ".discord-embed {\n\tcolor: #dcddde;\n\tdisplay: flex;\n\tmargin-top: 8px;\n\tmargin-bottom: 8px;\n\tfont-size: 13px;\n\tline-height: 150%;\n}\n\n.discord-light-theme .discord-embed {\n\tcolor: #2e3338;\n}\n\n.discord-embed .discord-left-border {\n\tbackground-color: #202225;\n\tflex-shrink: 0;\n\twidth: 4px;\n\tborder-radius: 4px 0 0 4px;\n}\n\n.discord-light-theme .discord-embed .discord-left-border {\n\tbackground-color: #e3e5e8;\n}\n\n.discord-embed .discord-embed-container {\n\tbackground-color: #2f3136;\n\tdisplay: flex;\n\tflex-direction: column;\n\tmax-width: 520px;\n\tpadding: 8px 16px 16px;\n\tborder: 1px solid rgba(46, 48, 54, 0.6);\n\tborder-radius: 0 4px 4px 0;\n}\n\n.discord-light-theme .discord-embed .discord-embed-container {\n\tbackground-color: rgba(249, 249, 249, 0.3);\n\tborder-color: rgba(205, 205, 205, 0.3);\n}\n\n.discord-embed .discord-embed-content {\n\tdisplay: flex;\n}\n\n.discord-embed .discord-embed-thumbnail {\n\tmax-width: 80px;\n\tmax-height: 80px;\n\tmargin-left: 16px;\n\tmargin-top: 8px;\n\tborder-radius: 4px;\n\tobject-fit: contain;\n\tobject-position: top center;\n}\n\n.discord-embed .discord-embed-author {\n\tcolor: #fff;\n\tdisplay: flex;\n\talign-items: center;\n\tfont-weight: 500;\n\tmargin-top: 8px;\n}\n\n.discord-light-theme .discord-embed .discord-embed-author {\n\tcolor: #4f545c;\n}\n\n.discord-embed .discord-embed-author a {\n\tcolor: #fff;\n}\n\n.discord-light-theme .discord-embed .discord-embed-author a {\n\tcolor: #4f545c;\n}\n\n.discord-embed .discord-embed-author .discord-author-image {\n\twidth: 20px;\n\theight: 20px;\n\tmargin-right: 8px;\n\tborder-radius: 50%;\n}\n\n.discord-embed .discord-embed-title {\n\tcolor: #fff;\n\tfont-size: 16px;\n\tfont-weight: 600;\n\tmargin-top: 8px;\n}\n\n.discord-embed .discord-embed-title a {\n\tcolor: #00b0f4;\n\tfont-weight: 600;\n}\n\n.discord-embed .discord-embed-description {\n\tmargin-top: 8px;\n}\n\n.discord-embed .discord-embed-image {\n\tmax-width: 100%;\n\tmargin-top: 16px;\n\tborder-radius: 4px;\n}\n\n.discord-embed .discord-embed-footer {\n\tcolor: #72767d;\n\tdisplay: flex;\n\talign-items: center;\n\tfont-size: 0.85em;\n\tmargin-top: 8px;\n}\n\n.discord-embed .discord-embed-footer .discord-footer-image {\n\tflex-shrink: 0;\n\twidth: 20px;\n\theight: 20px;\n\tmargin-right: 8px;\n\tborder-radius: 50%;\n}\n\n.discord-embed .discord-embed-footer .discord-footer-separator {\n\tcolor: #3b3c42;\n\tfont-weight: 700;\n\tmargin: 0 4px;\n}\n\n.discord-light-theme .discord-embed .discord-embed-footer .discord-footer-separator {\n\tcolor: #e4e4e4;\n}\n";
styleInject(css$6);

function DiscordEmbed(_ref) {
  var authorImage = _ref.authorImage,
      authorName = _ref.authorName,
      authorUrl = _ref.authorUrl,
      children = _ref.children,
      color = _ref.color,
      footerImage = _ref.footerImage,
      image = _ref.image,
      thumbnail = _ref.thumbnail,
      timestamp = _ref.timestamp,
      title = _ref.title,
      url = _ref.url;
  var slots = {
    'default': children,
    fields: findSlot(children, 'fields'),
    footer: findSlot(children, 'footer')
  };

  if (slots.fields) {
    if (! /*#__PURE__*/React.isValidElement(slots.fields)) {
      throw new Error('Element with slot name "fields" should be a valid DiscordEmbedFields component.');
    }

    slots["default"] = elementsWithoutSlot(slots["default"], 'fields');
  }

  if (slots.footer) slots["default"] = elementsWithoutSlot(slots["default"], 'footer');
  var content = {
    author: /*#__PURE__*/React__default['default'].createElement("div", {
      className: "discord-embed-author"
    }, authorImage ? /*#__PURE__*/React__default['default'].createElement("img", {
      src: authorImage,
      alt: "",
      className: "discord-author-image"
    }) : null, authorUrl ? /*#__PURE__*/React__default['default'].createElement("a", {
      href: authorUrl,
      target: "_blank",
      rel: "noopener noreferrer"
    }, authorName) : /*#__PURE__*/React__default['default'].createElement("span", null, authorName)),
    footer: /*#__PURE__*/React__default['default'].createElement("div", {
      className: "discord-embed-footer"
    }, slots.footer && footerImage ? /*#__PURE__*/React__default['default'].createElement("img", {
      src: footerImage,
      alt: "",
      className: "discord-footer-image"
    }) : null, /*#__PURE__*/React__default['default'].createElement("span", null, slots.footer, slots.footer && timestamp ? /*#__PURE__*/React__default['default'].createElement("span", {
      className: "discord-footer-separator"
    }, "\u2022") : null, timestamp ? /*#__PURE__*/React__default['default'].createElement("span", null, parseTimestamp(timestamp)) : null)),
    title: /*#__PURE__*/React__default['default'].createElement("div", {
      className: "discord-embed-title"
    }, url ? /*#__PURE__*/React__default['default'].createElement("a", {
      href: url,
      target: "_blank",
      rel: "noopener noreferrer"
    }, title) : /*#__PURE__*/React__default['default'].createElement("span", null, title))
  };
  return /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-embed"
  }, /*#__PURE__*/React__default['default'].createElement("div", {
    style: {
      backgroundColor: color
    },
    className: "discord-left-border"
  }), /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-embed-container"
  }, /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-embed-content"
  }, /*#__PURE__*/React__default['default'].createElement("div", null, authorName ? content.author : null, title ? content.title : null, /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-embed-description"
  }, slots["default"]), slots.fields, image ? /*#__PURE__*/React__default['default'].createElement("img", {
    src: image,
    alt: "",
    className: "discord-embed-image"
  }) : null), thumbnail ? /*#__PURE__*/React__default['default'].createElement("img", {
    src: thumbnail,
    alt: "",
    className: "discord-embed-thumbnail"
  }) : null), slots.footer || timestamp ? content.footer : null));
}

DiscordEmbed.propTypes = {
  authorImage: propTypes.string,
  authorName: propTypes.string,
  authorUrl: propTypes.string,
  children: propTypes.node,
  color: propTypes.string,
  footerImage: propTypes.string,
  image: propTypes.string,
  thumbnail: propTypes.string,
  timestamp: propTypes.oneOfType([propTypes.instanceOf(Date), propTypes.string]),
  title: propTypes.string,
  url: propTypes.string
};
DiscordEmbed.defaultProps = {
  author: 'User'
};

var css$5 = ".discord-embed .discord-embed-field {\n\tmin-width: 100%;\n\tmargin-top: 5px;\n}\n\n.discord-embed .discord-embed-field.discord-inline-field {\n\tflex-grow: 1;\n\tflex-basis: auto;\n\tmin-width: 100px;\n}\n\n.discord-embed .discord-embed-field .discord-field-title {\n\tcolor: #72767d;\n\tfont-weight: 500;\n\tmargin-bottom: 2px;\n}\n\n.discord-light-theme .discord-embed .discord-embed-field .discord-field-title {\n\tcolor: #747f8d;\n}\n";
styleInject(css$5);

function DiscordEmbedField(_ref) {
  var children = _ref.children,
      fieldTitle = _ref.fieldTitle,
      inline = _ref.inline;
  var classes = 'discord-embed-field';
  if (inline) classes += ' discord-inline-field';
  return /*#__PURE__*/React__default['default'].createElement("div", {
    className: classes
  }, /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-field-title"
  }, fieldTitle), children);
}

DiscordEmbedField.propTypes = {
  children: propTypes.node,
  fieldTitle: propTypes.string.isRequired,
  inline: propTypes.bool
};

var css$4 = ".discord-embed .discord-embed-fields {\n\tdisplay: flex;\n\tflex-wrap: wrap;\n\tmargin-top: 8px;\n}\n";
styleInject(css$4);

function DiscordEmbedFields(_ref) {
  var children = _ref.children;
  return /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-embed-fields"
  }, children);
}

DiscordEmbedFields.propTypes = {
  children: propTypes.node
};

var removeHash = function removeHash(hex) {
  return hex.charAt(0) === '#' ? hex.slice(1) : hex;
};

var parseHex = function parseHex(nakedHex) {
  var isShort = nakedHex.length === 3 || nakedHex.length === 4;

  var twoDigitHexR = isShort ? '' + nakedHex.slice(0, 1) + nakedHex.slice(0, 1) : nakedHex.slice(0, 2);
  var twoDigitHexG = isShort ? '' + nakedHex.slice(1, 2) + nakedHex.slice(1, 2) : nakedHex.slice(2, 4);
  var twoDigitHexB = isShort ? '' + nakedHex.slice(2, 3) + nakedHex.slice(2, 3) : nakedHex.slice(4, 6);
  var twoDigitHexA = (isShort ? '' + nakedHex.slice(3, 4) + nakedHex.slice(3, 4) : nakedHex.slice(6, 8)) || 'ff';

  // const numericA = +((parseInt(a, 16) / 255).toFixed(2));

  return {
    r: twoDigitHexR,
    g: twoDigitHexG,
    b: twoDigitHexB,
    a: twoDigitHexA
  };
};

var hexToDecimal = function hexToDecimal(hex) {
  return parseInt(hex, 16);
};

var hexesToDecimals = function hexesToDecimals(_ref) {
  var r = _ref.r,
      g = _ref.g,
      b = _ref.b,
      a = _ref.a;
  return {
    r: hexToDecimal(r),
    g: hexToDecimal(g),
    b: hexToDecimal(b),
    a: +(hexToDecimal(a) / 255).toFixed(2)
  };
};

var isNumeric = function isNumeric(n) {
  return !isNaN(parseFloat(n)) && isFinite(n);
}; // eslint-disable-line no-restricted-globals, max-len

var formatRgb = function formatRgb(decimalObject, parameterA) {
  var r = decimalObject.r,
      g = decimalObject.g,
      b = decimalObject.b,
      parsedA = decimalObject.a;

  var a = isNumeric(parameterA) ? parameterA : parsedA;

  return 'rgba(' + r + ', ' + g + ', ' + b + ', ' + a + ')';
};

/**
 * Turns an old-fashioned css hex color value into a rgb color value.
 *
 * If you specify an alpha value, you'll get a rgba() value instead.
 *
 * @param The hex value to convert. ('123456'. '#123456', ''123', '#123')
 * @param An alpha value to apply. (optional) ('0.5', '0.25')
 * @return An rgb or rgba value. ('rgb(11, 22, 33)'. 'rgba(11, 22, 33, 0.5)')
 */
var hexToRgba = function hexToRgba(hex, a) {
  var hashlessHex = removeHash(hex);
  var hexObject = parseHex(hashlessHex);
  var decimalObject = hexesToDecimals(hexObject);

  return formatRgb(decimalObject, a);
};

var build = hexToRgba;

var DiscordOptionsContext = /*#__PURE__*/React.createContext(DiscordDefaultOptions);

var css$3 = ".discord-message .discord-mention {\n\tcolor: #7289da;\n\tbackground-color: rgba(114, 137, 218, 0.1);\n\tfont-weight: 500;\n\tpadding: 0 1px;\n}\n\n.discord-message .discord-mention:hover {\n\tcolor: #fff;\n\tbackground-color: rgba(114, 137, 218, 0.7);\n}\n\n.discord-message.discord-highlight-mention {\n\tbackground-color: rgba(250, 166, 26, 0.05);\n\tposition: relative;\n}\n\n.discord-message.discord-highlight-mention::before {\n\tcontent: \"\";\n\tbackground-color: #faa61a;\n\tdisplay: block;\n\tposition: absolute;\n\ttop: 0;\n\tleft: 0;\n\tbottom: 0;\n\twidth: 2px;\n}\n\n.discord-message.discord-highlight-mention:hover {\n\tbackground-color: rgba(250, 166, 26, 0.1);\n}\n\n.discord-message.discord-highlight-mention .discord-mention {\n\tbackground-color: unset !important;\n}\n\n.discord-message.discord-highlight-mention .discord-mention:hover {\n\tcolor: #7289da;\n\ttext-decoration: underline;\n}\n";
styleInject(css$3);

function DiscordMention(_ref) {
  var children = _ref.children,
      color = _ref.color,
      profile = _ref.profile,
      type = _ref.type;
  var options = React.useContext(DiscordOptionsContext) || DiscordDefaultOptions;
  var user = options.profiles[profile] || {};
  var roleColor = user.roleColor || color;
  var $el = React.useRef(null);

  var setHoverColor = function setHoverColor() {
    return $el.current.style.backgroundColor = build(roleColor, 0.3);
  };

  var resetHoverColor = function resetHoverColor() {
    return $el.current.style.backgroundColor = build(roleColor, 0.1);
  };

  var colorStyle = !roleColor || type !== 'role' ? {} : {
    color: roleColor,
    backgroundColor: build(roleColor, 0.1)
  };
  React.useEffect(function () {
    if ($el.current && roleColor && type === 'role') {
      $el.current.addEventListener('mouseover', setHoverColor);
      $el.current.addEventListener('mouseout', resetHoverColor);
    }

    return function () {
      if ($el.current && roleColor && type === 'role') {
        $el.current.removeEventListener('mouseover', setHoverColor);
        $el.current.removeEventListener('mouseout', resetHoverColor);
      }
    };
  }, []);
  var slots = {
    'default': children
  };
  var mentionCharacter = type === 'channel' ? '#' : '@';

  if (!slots["default"]) {
    slots["default"] = type === 'user' && user.author ? user.author : type === 'channel' ? type : type.charAt(0).toUpperCase() + type.slice(1);
  }

  return /*#__PURE__*/React__default['default'].createElement("span", {
    style: colorStyle,
    className: "discord-mention",
    ref: $el
  }, mentionCharacter, slots["default"]);
}

DiscordMention.propTypes = {
  children: propTypes.node,
  color: propTypes.string,
  highlight: propTypes.bool,
  profile: propTypes.string,
  type: function type(props) {
    if (!['user', 'channel', 'role'].includes(props.type)) {
      return new RangeError('Type prop inside DiscordMention component must be either "user", "channel", or "role".');
    }
  }
};
DiscordMention.defaultProps = {
  type: 'user'
};

function _defineProperty(obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
}

var css$2 = ".discord-message .discord-author-info {\n\tcolor: #fff;\n\tdisplay: inline-flex;\n\talign-items: center;\n\tfont-size: 15px;\n}\n\n.discord-message .discord-author-info .discord-author-username {\n\tfont-size: 1.1em;\n\tfont-weight: 500;\n\tletter-spacing: 0.5px;\n}\n\n.discord-light-theme .discord-message .discord-author-info .discord-author-username {\n\tcolor: #23262a;\n}\n\n.discord-message .discord-author-info .discord-bot-tag {\n\tbackground-color: #7289da;\n\tfont-size: 0.65em;\n\tmargin-left: 5px;\n\tpadding: 3px;\n\tborder-radius: 3px;\n\tline-height: 100%;\n\ttext-transform: uppercase;\n}\n\n.discord-light-theme .discord-message .discord-author-info .discord-bot-tag {\n\tcolor: #fff;\n}\n\n\n.discord-compact-mode .discord-message .discord-author-info {\n\tdisplay: inline-flex;\n\tflex-direction: row-reverse;\n}\n\n.discord-compact-mode .discord-message .discord-author-info .discord-author-username {\n\tmargin-left: 4px;\n\tmargin-right: 4px;\n}\n\n.discord-compact-mode .discord-message .discord-author-info .discord-bot-tag {\n\tmargin-left: 0;\n\tmargin-right: 5px;\n\tpadding-left: 3px;\n\tpadding-right: 3px;\n\tfont-size: 0.6em;\n}\n";
styleInject(css$2);

function _extends() {
  _extends = Object.assign || function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };

  return _extends.apply(this, arguments);
}

var VerifiedBotCheck = function VerifiedBotCheck(props) {
  return /*#__PURE__*/React__default['default'].createElement("svg", _extends({
    "aria-label": "Verified Bot",
    className: "botTagVerified",
    "aria-hidden": "false",
    width: 16,
    height: 16,
    viewBox: "0 0 16 15.2"
  }, props), /*#__PURE__*/React__default['default'].createElement("path", {
    d: "M7.4,11.17,4,8.62,5,7.26l2,1.53L10.64,4l1.36,1Z",
    fill: "currentColor"
  }));
};

function AuthorInfo(_ref) {
  var author = _ref.author,
      bot = _ref.bot,
      roleColor = _ref.roleColor,
      verifiedBot = _ref.verifiedBot;
  return /*#__PURE__*/React__default['default'].createElement("span", {
    className: "discord-author-info"
  }, /*#__PURE__*/React__default['default'].createElement("span", {
    style: {
      color: roleColor
    },
    className: "discord-author-username"
  }, author), bot ? /*#__PURE__*/React__default['default'].createElement("span", {
    className: "discord-bot-tag"
  }, "Bot") : null, verifiedBot ? /*#__PURE__*/React__default['default'].createElement("span", {
    className: "discord-verified-bot-tag"
  }, VerifiedBotCheck, "BOT") : null);
}

AuthorInfo.propTypes = {
  author: propTypes.string,
  bot: propTypes.bool,
  verifiedBot: propTypes.bool,
  roleColor: propTypes.string
};

var css$1 = ".discord-message {\n\tcolor: #dcddde;\n\tdisplay: flex;\n\tfont-size: 0.9em;\n\tmargin: 1em 0;\n\tpadding: 0.25em 1em 0;\n}\n\n.discord-message:hover {\n\tbackground-color: #32353b;\n}\n\n.discord-light-theme .discord-message {\n\tcolor: #2e3338;\n}\n\n.discord-light-theme .discord-message:hover {\n\tbackground-color: #fafafa;\n}\n\n.discord-message a {\n\tcolor: #0096cf;\n\tfont-weight: normal;\n\ttext-decoration: none;\n}\n\n.discord-message a:hover {\n\ttext-decoration: underline;\n}\n\n.discord-light-theme .discord-message a {\n\tcolor: #00b0f4;\n}\n\n.discord-message .discord-author-avatar {\n\tmargin-top: 1px;\n\tmargin-right: 16px;\n\tmin-width: 40px;\n}\n\n.discord-message .discord-author-avatar img {\n\twidth: 40px;\n\theight: 40px;\n\tborder-radius: 50%;\n}\n\n.discord-message .discord-message-timestamp {\n\tcolor: #72767d;\n\tfont-size: 12px;\n\tmargin-left: 3px;\n}\n\n.discord-message .discord-message-edited {\n\tcolor: #72767d;\n\tfont-size: 10px;\n}\n\n.discord-message .discord-message-content {\n\twidth: 100%;\n\tline-height: 160%;\n\tfont-weight: normal;\n\toverflow-wrap: anywhere;\n}\n\n.discord-message .discord-message-body {\n\tposition: relative;\n}\n\n.discord-light-theme .discord-message .discord-message-timestamp,\n.discord-compact-mode .discord-message:hover .discord-message-timestamp,\n.discord-compact-mode.discord-light-theme .discord-message:hover .discord-message-timestamp {\n\tcolor: #99aab5;\n}\n\n.discord-compact-mode.discord-light-theme .discord-message .discord-message-timestamp {\n\tcolor: #d1d9de;\n}\n\n.discord-compact-mode .discord-message {\n\tmargin: 0.15em 0;\n\tpadding-left: 0.25em;\n\tpadding-right: 0.25em;\n}\n\n.discord-compact-mode .discord-author-avatar {\n\tdisplay: none;\n}\n\n.discord-compact-mode .discord-message-body {\n\tmargin-left: 0.25em;\n}\n";
styleInject(css$1);

function ownKeys(object, enumerableOnly) { var keys = Object.keys(object); if (Object.getOwnPropertySymbols) { var symbols = Object.getOwnPropertySymbols(object); if (enumerableOnly) symbols = symbols.filter(function (sym) { return Object.getOwnPropertyDescriptor(object, sym).enumerable; }); keys.push.apply(keys, symbols); } return keys; }

function _objectSpread(target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i] != null ? arguments[i] : {}; if (i % 2) { ownKeys(Object(source), true).forEach(function (key) { _defineProperty(target, key, source[key]); }); } else if (Object.getOwnPropertyDescriptors) { Object.defineProperties(target, Object.getOwnPropertyDescriptors(source)); } else { ownKeys(Object(source)).forEach(function (key) { Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key)); }); } } return target; }
var now = new Date();

function DiscordMessage(_ref) {
  var author = _ref.author,
      avatar = _ref.avatar,
      bot = _ref.bot,
      children = _ref.children,
      compactMode = _ref.compactMode,
      edited = _ref.edited,
      profileKey = _ref.profile,
      roleColor = _ref.roleColor,
      timestamp = _ref.timestamp;
  var options = React.useContext(DiscordOptionsContext) || DiscordDefaultOptions;
  var profileDefaults = {
    author: author,
    bot: bot,
    roleColor: roleColor
  };

  var resolveAvatar = function resolveAvatar(userAvatar) {
    return options.avatars[userAvatar] || userAvatar || options.avatars["default"];
  };

  var userProfile = options.profiles[profileKey] || {};
  userProfile.avatar = resolveAvatar(userProfile.avatar || avatar);

  var profile = _objectSpread(_objectSpread({}, profileDefaults), userProfile);

  var authorInfo = {
    comfy: /*#__PURE__*/React__default['default'].createElement("div", null, /*#__PURE__*/React__default['default'].createElement(AuthorInfo, {
      author: profile.author,
      bot: profile.bot,
      roleColor: profile.roleColor
    }), /*#__PURE__*/React__default['default'].createElement("span", {
      className: "discord-message-timestamp"
    }, parseTimestamp(timestamp))),
    compact: /*#__PURE__*/React__default['default'].createElement(React.Fragment, null, /*#__PURE__*/React__default['default'].createElement("span", {
      className: "discord-message-timestamp"
    }, parseTimestamp(timestamp)), /*#__PURE__*/React__default['default'].createElement(AuthorInfo, {
      author: profile.author,
      bot: profile.bot,
      roleColor: profile.roleColor
    }))
  };

  var checkHighlight = function checkHighlight(elements) {
    if (!Array.isArray(elements)) return false;
    return elements.some(function (_ref2) {
      var _ref2$props = _ref2.props,
          childProps = _ref2$props === void 0 ? {} : _ref2$props;
      return childProps.highlight && childProps.type !== 'channel';
    });
  };

  var messageClasses = 'discord-message';
  if (children && checkHighlight(children)) messageClasses += ' discord-highlight-mention';
  var slots = {
    'default': children,
    embeds: findSlot(children, 'embeds')
  };

  if (slots.embeds) {
    if (! /*#__PURE__*/React.isValidElement(slots.embeds)) {
      throw new Error('Element with slot name "embeds" should be a valid DiscordEmbed component.');
    }

    slots["default"] = elementsWithoutSlot(slots["default"], 'embeds');
  }

  return /*#__PURE__*/React__default['default'].createElement("div", {
    className: messageClasses
  }, /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-author-avatar"
  }, /*#__PURE__*/React__default['default'].createElement("img", {
    src: profile.avatar,
    alt: profile.author
  })), /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-message-content"
  }, !compactMode ? authorInfo.comfy : null, /*#__PURE__*/React__default['default'].createElement("div", {
    className: "discord-message-body"
  }, compactMode ? authorInfo.compact : null, slots["default"], edited ? /*#__PURE__*/React__default['default'].createElement("span", {
    className: "discord-message-edited"
  }, "(edited)") : null), slots.embeds));
}

DiscordMessage.propTypes = {
  author: propTypes.string,
  avatar: propTypes.string,
  bot: propTypes.bool,
  children: propTypes.node,
  compactMode: propTypes.bool,
  edited: propTypes.bool,
  profile: propTypes.string,
  roleColor: propTypes.string,
  timestamp: propTypes.oneOfType([propTypes.instanceOf(Date), propTypes.string])
};
DiscordMessage.defaultProps = {
  author: 'User',
  timestamp: now
};

var css = " @import url('https://fonts.googleapis.com/css?family=Roboto:400,500,700');\n\n.discord-messages {\n\tcolor: #fff;\n\tbackground-color: #36393e;\n\tfont-size: 16px;\n\tfont-family: 'Roboto', sans-serif;\n\tline-height: 170%;\n\tborder: 1px solid rgba(255, 255, 255, 0.05);\n}\n\n.discord-messages.discord-light-theme {\n\tcolor: #747f8d;\n\tbackground-color: #f7f7f7;\n\tborder-color: #dedede;\n}\n";
styleInject(css);

function DiscordMessages(_ref) {
  var children = _ref.children,
      compactMode = _ref.compactMode,
      lightTheme = _ref.lightTheme;
  var options = React.useContext(DiscordOptionsContext) || DiscordDefaultOptions;
  lightTheme = lightTheme === true || options.defaultTheme === 'light' && lightTheme !== false;
  compactMode = compactMode === true || options.defaultMode === 'compact' && compactMode !== false;
  var classes = 'discord-messages';
  if (lightTheme) classes += ' discord-light-theme';
  if (compactMode) classes += ' discord-compact-mode';
  var messages = React.Children.map(children, function (element, index) {
    return /*#__PURE__*/React.cloneElement(element, {
      compactMode: compactMode,
      key: index
    });
  });
  return /*#__PURE__*/React__default['default'].createElement("div", {
    className: classes
  }, messages);
}

DiscordMessages.propTypes = {
  children: propTypes.node,
  compactMode: propTypes.bool,
  lightTheme: propTypes.bool
};

exports.DiscordDefaultOptions = DiscordDefaultOptions;
exports.DiscordEmbed = DiscordEmbed;
exports.DiscordEmbedField = DiscordEmbedField;
exports.DiscordEmbedFields = DiscordEmbedFields;
exports.DiscordMention = DiscordMention;
exports.DiscordMessage = DiscordMessage;
exports.DiscordMessages = DiscordMessages;
exports.DiscordOptionsContext = DiscordOptionsContext;
//# sourceMappingURL=index.js.map
